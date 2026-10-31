import base64
import io
import json
import tempfile
import unittest
from email.message import Message
from pathlib import Path
from unittest.mock import patch
from binding import Refusal, decode_http, load, run_scenario
from row import Route

class Sessions(unittest.TestCase):
    def test_cookies_stay_in_member_route_and_credentials_are_redacted(self):
        sent=[]
        class Reply:
            status=200
            def __init__(self):
                self.headers=Message(); self.headers['content-type']='application/json'
                self.headers['set-cookie']='appsession=secret; Path=/; Secure; HttpOnly'
                self.headers['set-cookie']='__Host-mini_spk_session=evil; Path=/; Secure'
            def read(self,n): return b'{"token":"secret"}'
            def getheader(self,k,default=None): return self.headers.get(k,default)
            def getheaders(self): return list(self.headers.items())
            def info(self): return self.headers
        class Conn:
            def __init__(self,*args): pass
            def request(self,method,path,body,headers): sent.append(headers)
            def getresponse(self): return Reply()
            def close(self): pass
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp); (path/'browser.token').write_text('member-token')
            journal=io.StringIO(); declaration=load('gogs'); declaration['auth']={'appCookies':'retain'}
            route=Route(path,declaration,journal)
            request={'method':'GET','path':'token','query':'','headers':{},'body':b'', 'redact':True}
            with patch('row.UnixHTTP',Conn),patch.object(route,'retain',lambda x:journal.write(json.dumps(x)+'\n')):
                route.http(request); route.http(request)
            self.assertIn('appsession=secret',sent[1]['Cookie'])
            self.assertIn('__Host-mini_spk_session=member-token',sent[1]['Cookie'])
            self.assertNotIn('evil',sent[1]['Cookie'])
            self.assertEqual(route.cookie_values('token')['appsession'],'secret')
            self.assertEqual(Route(path,load('gogs'),io.StringIO()).cookie_values('token'),{})
            omitted=Route(path,load('gogs'),io.StringIO())
            with patch('row.UnixHTTP',Conn),patch.object(omitted,'retain'):
                omitted.http(request); omitted.http(request)
            self.assertNotIn('appsession',sent[-1]['Cookie'])
            self.assertEqual(omitted.cookie_values('token'),{})
            self.assertNotIn('secret',journal.getvalue())
            self.assertNotIn(base64.b64encode(b'{"token":"secret"}').decode(),journal.getvalue())

    def test_explicit_json_content_type_and_caldav_property_status(self):
        d=load('gogs'); op=d['operations']['user.read']
        with self.assertRaisesRegex(Refusal,'app-content-type'): decode_http(d,op,(200,{'content-type':'text/html'},b'{"ok":true}'))
        op['binding']['acceptedContentTypes']=['text/html']
        self.assertEqual(decode_http(d,op,(200,{'content-type':'text/html; charset=utf-8'},b'{"ok":true}')),{'ok':True})
        op['binding'].update(decode='caldav-multistatus',status=[207])
        xml=b'<d:multistatus xmlns:d="DAV:" xmlns:c="urn:ietf:params:xml:ns:caldav"><d:response><d:href>/cal/a.ics</d:href><d:propstat><d:prop><d:getetag>"a"</d:getetag><c:calendar-data>BEGIN:VCALENDAR</c:calendar-data></d:prop><d:status>HTTP/1.1 200 OK</d:status></d:propstat><d:propstat><d:prop><d:resourcetype/></d:prop><d:status>HTTP/1.1 404 Not Found</d:status></d:propstat></d:response></d:multistatus>'
        self.assertEqual(decode_http(d,op,(207,{},xml)),[{'href':'/cal/a.ics','etag':'"a"','calendarData':'BEGIN:VCALENDAR'}])
        with self.assertRaises(Refusal): decode_http(d,op,(207,{},xml.replace(b'200 OK',b'404 Not Found')))

    def test_text_readback_assertion_checks_contents(self):
        class Engine:
            d={'name':'test','qualification':[{'id':'read','op':'read','args':{},'assert':[{'path':[],'containsText':{'context':'runId'}}]}]}
            context={'runId':'needle'}
            def tool_call(self,*args): return {'structuredContent':{'value':'hay needle hay'}}
        self.assertEqual(run_scenario(Engine()),{'read':'hay needle hay'})
        e=Engine(); e.context={'runId':'absent'}
        with self.assertRaisesRegex(Refusal,'readback-mismatch'): run_scenario(e)
