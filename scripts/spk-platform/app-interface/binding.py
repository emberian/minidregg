"""Executable conformance model for mini-app-interface-v1, NOT a policy/runtime service.

The declarations are the source of tool schemas, encodings and qualification rows.
This Python driver stays in the qualification harness. Production custody/admission
remain in Lean/Rust; see docs/APP-INTERFACE-2026-10-28.md for the native receiving seam.
"""
import base64
import csv
import hashlib
import io
import json
import re
import time
import urllib.parse
import xml.etree.ElementTree as ET
from pathlib import Path

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[3] / 'apps' / 'interfaces'


class Refusal(Exception):
    def __init__(self, name, detail=''):
        self.name, self.detail = name, detail
        super().__init__(name + (': ' + detail if detail else ''))


class Uncertain(Refusal):
    """A dispatched mutation may have happened; never retry it automatically."""


def load(name):
    if not re.fullmatch(r'[a-z][a-z0-9-]*', name) or not (ROOT / (name + '.json')).is_file():
        raise Refusal('interface-unknown')
    d = json.loads((ROOT / (name + '.json')).read_text())
    check_declaration(d)
    return d


def check_declaration(d):
    if d['format'] != 'mini-app-interface-v1':
        raise Refusal('interface-version-unsupported')
    contract = json.loads((ROOT / 'format.schema.json').read_text())
    if not Draft202012Validator(contract).is_valid(d):
        raise Refusal('declaration-invalid')
    if d.get('auth', {}).get('appCookies', 'omit') not in ('omit', 'retain'):
        raise Refusal('declaration-invalid', 'unknown app cookie policy')
    for op in d['operations'].values():
        ids = [step['id'] for step in op.get('prepare', [])]
        if len(ids) != len(set(ids)):
            raise Refusal('declaration-invalid', 'duplicate preparation id')
        for key in ('input', 'output'):
            Draft202012Validator.check_schema({**op[key], '$defs': d['$defs']})
        b = op['binding']
        if b['protocol'] == 'http' and sum(k in b for k in ('json', 'text', 'base64', 'form', 'multipart')) > 1:
            raise Refusal('declaration-invalid', 'ambiguous HTTP body')
        if 'emptyValue' in b and b.get('decode') != 'json':
            raise Refusal('declaration-invalid', 'empty value requires JSON decoding')
        if b.get('decode') == 'json-string-fragment' and (not op.get('internal') or op['write']):
            raise Refusal('declaration-invalid', 'auth fragment must be an internal read')
        if any(name not in SAFE_RESPONSE_HEADERS for name in b.get('responseHeaders', {}).values()):
            raise Refusal('declaration-invalid', 'response header forbidden')
    # Relations may only read. Reject cycles before a row can dispatch anything.
    def visit(name, ancestors):
        if name not in d['operations'] or name in ancestors:
            raise Refusal('declaration-invalid', 'unknown or cyclic operation dependency')
        for req in d['operations'][name].get('requires', []) + d['operations'][name].get('prepare', []):
            if d['operations'].get(req['op'], {}).get('write', True):
                raise Refusal('declaration-invalid', 'relation dependency must read')
            visit(req['op'], ancestors | {name})
    for name in d['operations']:
        visit(name, set())
    seen = set()
    for step in d['qualification']:
        if step['id'] in seen or step['op'] not in d['operations']:
            raise Refusal('declaration-invalid', 'invalid qualification step')
        if 'await' in step and d['operations'][step['op']]['write']:
            raise Refusal('declaration-invalid', 'readiness wait must read')
        seen.add(step['id'])


def digest(d):
    return hashlib.sha256(json.dumps(d, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def relative_path(s):
    # Reject aliases before any percent encoding; one path has one interpretation.
    if not isinstance(s, str) or not s or any(c in s for c in ('\\', '%', '?', '#')):
        raise Refusal('path-invalid')
    if any(ord(c) < 32 or ord(c) == 127 for c in s) or any(p in ('', '.', '..') for p in s.split('/')):
        raise Refusal('path-invalid')
    return '/'.join(urllib.parse.quote(p, safe='-._~') for p in s.split('/'))


def validate(d, schema, value, phase='input'):
    errors = list(Draft202012Validator({**schema, '$defs': d['$defs']}).iter_errors(value))
    if errors:
        # Do not echo values: arguments and app responses may contain private data.
        raise Refusal(phase + '-schema', '/'.join(map(str, errors[0].absolute_path)))
    def formats(s, v):
        if '$ref' in s:
            return formats(d['$defs'][s['$ref'].split('/')[-1]], v)
        if 'uniqueBy' in s:
            key = s['uniqueBy']
            if not isinstance(key, str) or not key or not isinstance(v, list) or len(v) > 1000:
                raise Refusal(phase + '-unique-key')
            seen = set()
            for entry in v:
                if not isinstance(entry, dict) or key not in entry or type(entry[key]) not in (str, int):
                    raise Refusal(phase + '-unique-key')
                identity = (type(entry[key]), entry[key])
                if identity in seen:
                    raise Refusal(phase + '-unique-key')
                seen.add(identity)
        if s.get('format') == 'relative-path':
            relative_path(v)
        if s.get('contentEncoding') == 'base64':
            try:
                b = base64.b64decode(v, validate=True)
            except (ValueError, TypeError):
                raise Refusal('binary-encoding') from None
            if base64.b64encode(b).decode() != v:
                raise Refusal('binary-encoding')
            limit = 'bodyBytes' if phase == 'input' else 'replyBytes'
            if len(b) > d['limits'][limit]:
                raise Refusal('body-over-bound' if phase == 'input' else 'reply-over-bound')
        if isinstance(v, dict):
            for k, sub in s.get('properties', {}).items():
                if k in v:
                    formats(sub, v[k])
        if isinstance(v, list) and 'items' in s:
            for x in v:
                formats(s['items'], x)
    formats(schema, value)


def resolve(x, args, context, results=None):
    if isinstance(x, list):
        return [resolve(v, args, context, results) for v in x]
    if not isinstance(x, dict):
        return x
    if set(x) == {'arg'}:
        return args[x['arg']]
    if set(x) == {'cookie'}:
        value = context.get('cookies', {}).get(x['cookie'])
        if value is None:
            raise Refusal('app-cookie-required', x['cookie'])
        return value
    if set(x) == {'context'}:
        return context[x['context']]
    if set(x) == {'result'}:
        v = results
        for p in x['result']:
            v = v[p]
        return v
    if set(x) == {'sha256'}:
        value = resolve(x['sha256'], args, context, results)
        if not isinstance(value, str):
            raise Refusal('hash-input-invalid')
        return hashlib.sha256(value.encode('utf-8')).hexdigest()
    if set(x) == {'concat'}:
        return ''.join(str(resolve(v, args, context, results)) for v in x['concat'])
    if set(x) == {'csv'}:
        rows = resolve(x['csv'], args, context, results)
        if not isinstance(rows, list) or any(
                not isinstance(row, list) or any(not isinstance(cell, str) for cell in row)
                for row in rows):
            raise Refusal('csv-input-invalid')
        out = io.StringIO(newline='')
        csv.writer(out, lineterminator='\r\n').writerows(rows)
        return out.getvalue()
    if set(x) == {'path'} and isinstance(x['path'], list):
        return encode_path(x['path'], args)
    return {k: resolve(v, args, context, results) for k, v in x.items()}


def encode_path(parts, args):
    encoded = []
    for part in parts:
        if isinstance(part, str):
            encoded.append(part)
            continue
        value = str(args[part['arg']])
        if part['encoding'] == 'path':
            encoded.append(relative_path(value))
        elif part['encoding'] == 'segment':
            if value in ('.', '..') or '/' in value or '\\' in value:
                raise Refusal('path-invalid')
            encoded.append(urllib.parse.quote(value, safe='-._~'))
        else:
            raise Refusal('binding-encoding-unsupported')
    return ''.join(encoded)


def multipart(parts, args, context, results):
    encoded = []
    for part in parts:
        name, filename, content_type = part['name'], resolve(part.get('filename'), args, context, results), part.get('contentType')
        for field in (name, filename, content_type):
            if field is not None and (not isinstance(field, str) or any(c in field for c in '\r\n\x00"\\')):
                raise Refusal('multipart-metadata-invalid')
        disposition = 'Content-Disposition: form-data; name="' + name + '"'
        if filename is not None:
            disposition += '; filename="' + filename + '"'
        headers = disposition + '\r\n' + ('Content-Type: ' + content_type + '\r\n' if content_type else '')
        if 'base64' in part:
            try:
                data = base64.b64decode(resolve(part['base64'], args, context, results), validate=True)
            except (ValueError, TypeError):
                raise Refusal('binary-encoding') from None
        else:
            value = resolve(part['text'], args, context, results)
            if not isinstance(value, str):
                raise Refusal('text-encoding')
            data = value.encode()
        encoded.append(headers.encode() + b'\r\n' + data)
    seed = hashlib.sha256(b'\x00'.join(encoded)).hexdigest()
    boundary = 'mini-' + seed
    while any(boundary.encode() in part for part in encoded):
        boundary += '-x'
    marker = boundary.encode()
    body = b''.join(b'--' + marker + b'\r\n' + part + b'\r\n' for part in encoded) + b'--' + marker + b'--\r\n'
    return body, 'multipart/form-data; boundary=' + boundary


def encode_http(d, op, args, context, results=None):
    b = op['binding']
    value = lambda x: resolve(x, args, context, results)
    headers = value(b.get('headers', {}))
    if 'json' in b:
        body = json.dumps(value(b['json']), separators=(',', ':'), ensure_ascii=False).encode()
        headers['content-type'] = 'application/json'
    elif 'base64' in b:
        body = base64.b64decode(value(b['base64']), validate=True)
    elif 'form' in b:
        fields = value(b['form'])
        if any(not isinstance(v, (str, int, float, bool)) for v in fields.values()):
            raise Refusal('form-value-invalid')
        body = urllib.parse.urlencode(fields).encode()
        headers['content-type'] = 'application/x-www-form-urlencoded'
    elif 'multipart' in b:
        body, headers['content-type'] = multipart(b['multipart'], args, context, results)
    else:
        text = value(b.get('text', ''))
        if not isinstance(text, str):
            raise Refusal('text-encoding')
        body = text.encode()
    if len(body) > d['limits']['bodyBytes']:
        raise Refusal('body-over-bound')
    for k, v in headers.items():
        if not isinstance(v, str) or any(c in k + v for c in '\r\n\x00'):
            raise Refusal('header-invalid')
    query = urllib.parse.urlencode(value(b.get('query', {})), quote_via=urllib.parse.quote)
    request = {'method': b['method'], 'path': encode_path(b['path'], args), 'query': query,
               'headers': headers, 'body': body}
    if op.get('internal') or op.get('prepare'):
        request['redact'] = True
    return request


def safe_xml_text(body, codec):
    # Decode before scanning so an alternate XML encoding cannot hide a DTD.
    try:
        text = body.decode('utf-8')
    except UnicodeError:
        raise Refusal(codec + '-response-invalid') from None
    if '\x00' in text:
        raise Refusal(codec + '-response-invalid')
    if '<!DOCTYPE' in text.upper() or '<!ENTITY' in text.upper():
        raise Refusal(codec + '-xml-unsafe')
    return text


def dav_decode(body, calendar=False):
    text = safe_xml_text(body, 'dav')
    try:
        root = ET.fromstring(text)
        if root.tag != '{DAV:}multistatus':
            raise ValueError()
        result = []
        for response in root.findall('{DAV:}response'):
            href = response.findtext('{DAV:}href')
            if not href:
                raise ValueError()
            props = {}
            for ps in response.findall('{DAV:}propstat'):
                status = ps.findtext('{DAV:}status', '')
                if re.fullmatch(r'HTTP/\S+ 2\d\d(?: .*)?', status):
                    props.update({p.tag: p for p in ps.find('{DAV:}prop')})
                elif ' 404 ' not in status:
                    raise Refusal('dav-property-refused')
            if calendar:
                data = props.get('{urn:ietf:params:xml:ns:caldav}calendar-data')
                etag = props.get('{DAV:}getetag')
                if data is None or etag is None or not etag.text:
                    raise Refusal('caldav-property-missing')
                result.append({'href': href, 'etag': etag.text, 'calendarData': data.text or ''})
                continue
            if '{DAV:}resourcetype' not in props:
                raise Refusal('dav-property-missing')
            size = props.get('{DAV:}getcontentlength')
            etag = props.get('{DAV:}getetag')
            result.append({'href': href, 'collection': props['{DAV:}resourcetype'].find('{DAV:}collection') is not None,
                           'bytes': int(size.text) if size is not None and size.text else None,
                           'etag': etag.text if etag is not None else None})
        return result
    except (ET.ParseError, ValueError, TypeError):
        raise Refusal('dav-response-invalid') from None


def rss_decode(body, limit):
    xml = safe_xml_text(body, 'rss')
    try:
        root = ET.fromstring(xml)
        if root.tag != 'rss' or root.get('version') != '2.0':
            raise ValueError()
        channels = root.findall('channel')
        if len(channels) != 1:
            raise ValueError()
        entries = channels[0].findall('item')
        if len(entries) > limit:
            raise Refusal('rss-items-over-bound')
        result = []
        for item in entries:
            def field(name):
                elements = item.findall(name)
                if len(elements) > 1 or any(len(e) for e in elements):
                    raise ValueError()
                return (elements[0].text or '') if elements else None
            identity = field('guid') or field('link')
            if not identity:
                raise ValueError()
            enclosures = item.findall('enclosure')
            if len(enclosures) > 1:
                raise ValueError()
            enclosure = None
            if enclosures:
                e = enclosures[0]
                length = e.get('length', '')
                if not e.get('url') or not e.get('type') or not re.fullmatch(r'[0-9]+', length):
                    raise ValueError()
                enclosure = {'url': e.get('url'), 'bytes': int(length), 'type': e.get('type')}
            result.append({'id': identity, 'title': field('title'), 'link': field('link'),
                           'description': field('description'), 'published': field('pubDate'),
                           'enclosure': enclosure})
        return result
    except (ET.ParseError, ValueError, TypeError):
        raise Refusal('rss-response-invalid') from None


SAFE_RESPONSE_HEADERS = frozenset({'etag', 'last-modified', 'content-type', 'content-length',
                                   'x-sandstorm-app-data-version'})


def decode_http(d, op, response):
    projection = op['binding'].get('responseHeaders')
    if projection is not None and any(name not in SAFE_RESPONSE_HEADERS for name in projection.values()):
        raise Refusal('binding-response-header-forbidden')
    value = decode_http_body(d, op, response)
    if projection is None:
        return value
    headers = {}
    for field, name in projection.items():
        header = response[1].get(name)
        if header is None:
            raise Refusal('app-response-header-missing', name)
        if not isinstance(header, str) or len(header) > 4096 or any(ord(c) < 32 or ord(c) == 127 for c in header):
            raise Refusal('app-response-header-invalid', name)
        headers[field] = header
    return {'body': value, 'headers': headers}


def decode_http_body(d, op, response):
    status, headers, body = response
    if len(body) > d['limits']['replyBytes']:
        raise Refusal('reply-over-bound')
    if status not in op['binding']['status']:
        if op['write'] and status >= 500:
            raise Uncertain('app-server-error-after-dispatch', str(status))
        raise Refusal({401: 'app-auth-required', 403: 'app-permission-denied', 404: 'app-not-found',
                       409: 'app-conflict', 412: 'app-precondition-failed'}.get(status, 'app-http-status'), str(status))
    mode = op['binding']['decode']
    try:
        if mode == 'json':
            if 'json' not in headers.get('content-type', '').lower() and headers.get('content-type', '').split(';')[0].strip().lower() not in op['binding'].get('acceptedContentTypes', []):
                raise Refusal('app-content-type')
            if body == b'' and 'emptyValue' in op['binding']:
                literal = json.dumps(op['binding']['emptyValue'], ensure_ascii=False).encode()
                if len(literal) > d['limits']['replyBytes']:
                    raise Refusal('reply-over-bound')
                return json.loads(literal)
            return json.loads(body)
        if mode == 'text':
            return body.decode('utf-8')
        if mode == 'json-lines':
            return [json.loads(line) for line in body.decode('utf-8').splitlines() if line.strip()]
        if mode == 'json-string-fragment':
            fragment = op['binding'].get('fragment', {})
            prefix, suffix = fragment.get('prefix'), fragment.get('suffix')
            if not op.get('internal') or op['write'] or not isinstance(prefix, str) or not isinstance(suffix, str) or not (1 <= len(prefix) <= 256 and 1 <= len(suffix) <= 64):
                raise Refusal('binding-auth-fragment-invalid')
            text = body.decode('utf-8')
            if text.count(prefix) != 1:
                raise Refusal('app-auth-fragment-invalid')
            fragment_text = text.split(prefix, 1)[1]
            value, end = json.JSONDecoder().raw_decode(fragment_text)
            if not isinstance(value, str) or not fragment_text[end:].lstrip().startswith(suffix):
                raise Refusal('app-auth-fragment-invalid')
            value.encode('utf-8')
            return value
        if mode == 'base64':
            return {'contentBase64': base64.b64encode(body).decode()}
        if mode == 'status':
            return {'status': status}
        if mode == 'rss':
            return rss_decode(body, d['limits']['snapshotDocuments'])
        if mode in ('dav-multistatus', 'caldav-multistatus'):
            return dav_decode(body, calendar=mode == 'caldav-multistatus')
        raise Refusal('binding-decoder-unsupported')
    except (ValueError, UnicodeError):
        raise Refusal('app-json-invalid') from None


def tools(d):
    """MCP shapes for an already member/session/package-bound catalog. No ambient route argument."""
    return [{'name': 'mini_' + d['name'] + '_' + name.replace('.', '_'),
             'description': op['description'],
             'inputSchema': {**op['input'], '$defs': d['$defs']},
             'outputSchema': {'type': 'object', 'properties': {'value': op['output']},
                              'required': ['value'], 'additionalProperties': False, '$defs': d['$defs']},
             'annotations': {'readOnlyHint': not op['write'], 'idempotentHint': False},
             '_meta': {'interfaceDigest': digest(d), 'packageId': d['packageId'], 'operation': name}}
            for name, op in d['operations'].items() if not op.get('internal', False)]


class Engine:
    def __init__(self, declaration, transport, context):
        self.d, self.transport, self.context = declaration, transport, context

    def call(self, name, args):
        op = self.d['operations'].get(name)
        if op is None:
            raise Refusal('operation-unknown')
        validate(self.d, op['input'], args)
        results = {}
        for step in op.get('prepare', []):
            results[step['id']] = self.call(step['op'], resolve(step['args'], args, self.context, results))
        for req in op.get('requires', []):
            snapshot = self.call(req['op'], resolve(req['args'], args, self.context))
            for r in req.get('exists', []):
                where = resolve(r['where'], args, self.context)
                matches = [v for v in snapshot[r['collection']] if all(v.get(k) == x for k, x in where.items())]
                if len(matches) != 1:
                    raise Refusal('relation-not-visible-or-mismatched', r['collection'])
            for check in req.get('assert', []):
                got = snapshot
                for p in check['path']:
                    got = got[p]
                if got != resolve(check['equals'], args, self.context):
                    raise Refusal('precondition-failed', req['op'])
        try:
            b = op['binding']
            if b['protocol'] == 'http':
                context = {**self.context, 'cookies': self.transport.cookie_values(encode_path(b['path'], args)) if hasattr(self.transport, 'cookie_values') else {}}
                value = decode_http(self.d, op, self.transport.http(encode_http(self.d, op, args, context, results)))
            elif b['protocol'] == 'ddp':
                value = self.transport.ddp(b, args, self.context, op['write'])
            else:
                raise Refusal('binding-protocol-unsupported')
            if 'projection' in op:
                p = op['projection']; where = resolve(p['where'], args, self.context)
                values = value.get(p['collection']) if isinstance(value, dict) else None
                if p.get('values', False):
                    if not isinstance(values, dict):
                        raise Refusal('projection-shape-invalid')
                    values = list(values.values())
                if not isinstance(values, list) or any(not isinstance(v, dict) for v in values):
                    raise Refusal('projection-shape-invalid')
                value = [v for v in values if all(v.get(k) == x for k, x in where.items())]
            validate(self.d, op['output'], value, 'output')
            return value
        except Uncertain:
            raise
        except (OSError, EOFError) as e:
            cls = Uncertain if op['write'] else Refusal
            raise cls('dispatch-uncertain' if op['write'] else 'transport-closed') from e
        except Refusal as e:
            # A malformed success reply is not evidence that a mutation did not occur.
            if op['write'] and e.name in ('output-schema', 'output-unique-key', 'app-json-invalid', 'app-content-type', 'reply-over-bound', 'app-response-header-missing', 'app-response-header-invalid'):
                raise Uncertain('reply-uninterpretable', e.name) from e
            raise

    def tool_call(self, name, args):
        """MCP result projection for the prototype; the row uses this same entry point."""
        spec = next((t for t in tools(self.d) if t['name'] == name), None)
        if spec is None:
            raise Refusal('operation-unknown')
        value = {'value': self.call(spec['_meta']['operation'], args)}
        return {'structuredContent': value, 'content': [{'type': 'text', 'text': json.dumps(value)}],
                'isError': False}


def scenario_assertions(step, value, context, results):
    def json_equal(a, b):
        # Python considers True == 1, unlike the native JSON value contract.
        return json.dumps(a, sort_keys=True) == json.dumps(b, sort_keys=True)
    for check in step.get('assert', []):
        if 'contains' in check:
            expected = resolve(check['contains'], {}, context, results)
            ok = isinstance(value, list) and any(
                (isinstance(v, dict) and all(k in v and json_equal(v[k], x) for k, x in expected.items()))
                if isinstance(expected, dict) else json_equal(v, expected) for v in value)
        else:
            got = value
            try:
                for p in check['path']:
                    got = got[p]
            except (KeyError, IndexError, TypeError):
                raise Refusal('readback-mismatch', step['id']) from None
            if check.get('exists') is True:
                ok = True
            elif 'containsText' in check:
                expected = resolve(check['containsText'], {}, context, results)
                ok = isinstance(got, str) and isinstance(expected, str) and expected in got
            else:
                ok = got == resolve(check['equals'], {}, context, results)
        if not ok:
            raise Refusal('readback-mismatch', step['id'])


def compound_readback(op):
    """A returned event after a compound mutation can be its only observable readback."""
    binding = op.get('binding', {})
    if binding.get('protocol') != 'conversation':
        return False
    steps = binding['steps']
    sent = [i for i, step in enumerate(steps) if any(k in step for k in ('send', 'emit', 'http'))]
    if not sent:
        return False
    captures = set()
    for step in steps[max(sent) + 1:]:
        if 'receive' in step and step['receive'].get('where'):
            captures.add(step['id'])
        for terminal in step.get('receiveAll', []):
            if terminal.get('where'):
                captures.add(terminal['id'])

    def uses_capture(value):
        if isinstance(value, dict):
            if set(value) == {'result'}:
                path = value['result']
                return isinstance(path, list) and bool(path) and path[0] in captures
            return any(uses_capture(v) for v in value.values())
        return isinstance(value, list) and any(uses_capture(v) for v in value)

    return uses_capture(binding['result'])


def require_write_readback(d):
    """Qualification is stricter than offering useful read-only tools."""
    wrote = False
    for step in d['qualification']:
        op = d['operations'][step['op']]
        if op['write']:
            wrote = True
            if step.get('assert') and compound_readback(op):
                return
        elif wrote and step.get('assert'):
            return
    raise Refusal('qualification-write-readback-absent')


def run_scenario(engine):
    results = {}
    for step in engine.d['qualification']:
        args = resolve(step['args'], {}, engine.context, results)
        tool_name = 'mini_' + engine.d['name'] + '_' + step['op'].replace('.', '_')
        wait = step.get('await')
        if wait and engine.d['operations'][step['op']]['write']:
            raise Refusal('declaration-invalid', 'readiness wait must read')
        for attempt in range(wait['attempts'] if wait else 1):
            try:
                value = engine.tool_call(tool_name, args)['structuredContent']['value']
                candidate = {**results, step['id']: value}
                scenario_assertions(step, value, engine.context, candidate)
                results = candidate
                break
            except Refusal as e:
                # No transport reconnect, mutation replay, auth retry, or generic
                # error suppression. Only this declared finite readiness condition.
                retryable = e.name == 'readback-mismatch' or (
                    e.name == 'app-http-status' and e.detail in {
                        str(status) for status in (wait or {}).get('retryStatuses', [])})
                if not wait or isinstance(e, Uncertain) or not retryable or attempt + 1 == wait['attempts']:
                    raise
                time.sleep(wait['intervalSeconds'])
    return results
