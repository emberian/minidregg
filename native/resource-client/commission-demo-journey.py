#!/usr/bin/env python3
"""Commission Board D1, one fresh native Store, signed mini activity/seat turns.

CB1: post, capped fleet claim/submit, reviewer call, receipt exchange, paid once.
CB5: cancel unclaimed/refund; cancel claimed refused by the Board law's leaf.
CB7: no review call or approval seat; the claim seat's deadline pays its payee.
CBP: asserted double-pay mutation in the captured escrow, refused `unfunded`.

The driver transports and checks native outcomes. It does not implement a ledger,
review policy or admission decision. Board calls and seat turns are separate
operations; the poster retains the approval invitation. See world/commission/README.md.
"""
import argparse
import hashlib
import json
import pathlib
import sys
import traceback

from activity_world import (World, MAXIMUM, PERMIT_ALL, nat, record, variant,
                            eq, all_of, any_of, eq_slots, cap, op_id)

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parent.parent
REWARD = 50


def label(value):
    return {'tag': 'label', 'value': value}


def state_type(*fields):
    ty = {'tag': 'emptyRow'}
    for name in reversed(fields):
        ty = {'tag': 'field', 'name': name, 'member': {'tag': 'natural'}, 'tail': ty}
    return ty


def field(data, name):
    return next(f['value'] for f in data['fields'] if f['name'] == name)


def balances(view):
    return {(b['account'], b['asset']): int(b['balance']) for b in view.get('balances', [])}


class Commission:
    def __init__(self, w):
        self.w = w
        self.pins = {}
        self.seats = []
        self.gold_totals = []
        self.receipts = {}
        self.mutations = []

    def publish(self, name, entry, modules, seat=False):
        w = self.w
        if seat:
            pub = w.root / ('publication-' + name)
            pub.mkdir()
            spec = {'schema': 'dregg.objective-bend.package-input.v1', 'edition': 'objective-bend-1',
                    'modules': modules, 'entryModule': str(len(modules) - 1), 'entryDefinition': entry}
            (pub / 'spec.json').write_text(json.dumps(spec))
            out = w.last_json(w.sh('publication-' + name, w.host, w.config, 'objective-publication',
                                   pub / 'spec.json', 'seat', pub / 'out'))
            pin = out['artifactId']
            artifact = {k: (pub / 'out' / f'{k}.bin').read_bytes().hex() for k in ('artifact', 'package')}
            self.seat_turn('publish-' + name, dict(artifact, kind='publish', payer=w.SPONSOR_ACCOUNT),
                           account_cap=w.SPONSOR_SPEND)
        else:
            pin, artifact = w.publication('publication-' + name, modules, str(len(modules) - 1), entry)
            w.turn('publish-' + name, w.sponsor, dict(artifact, kind='publish', payer=w.SPONSOR_ACCOUNT,
                                                     payerCapability=w.SPONSOR_SPEND), 'installed')
        self.pins[name] = pin
        return pin

    def module(self, name, path, imports=()):
        return {'name': name, 'sourcePath': str(REPO / path), 'imports': list(imports)}

    @staticmethod
    def imported(alias, path, index):
        return {'alias': alias, 'path': path, 'module': str(index)}

    def packages(self, planted=False):
        p = self.module('Protocol', 'world/commission/Protocol.obend')
        for name, entry in [('Board', 'claim'), ('Agent', 'run'), ('Guild', 'membership')]:
            self.publish(name, entry, [p, self.module(name, f'world/commission/{name}.obend',
                         [self.imported('P', './Protocol.obend', 0)])])
        self.publish('Review', 'review', [p,
            self.module('CatalogReview', 'world/workshop/CatalogReview.obend'),
            self.module('Review', 'world/commission/Review.obend', [
                self.imported('P', './Protocol.obend', 0),
                self.imported('Catalog', './CatalogReview.obend', 1)])])
        self.escrow_package('Escrow')
        if planted:
            self.escrow_package('DoublePay', plant=True)

    def escrow_package(self, name, plant=False):
        bounty = self.module('BountyEscrow', 'world/bounty/BountyEscrow.obend',
                             [self.imported('Order', './NatOrder.obend', 0)])
        if plant:
            source = pathlib.Path(bounty['sourcePath']).read_text()
            old = 'exchange(wholeMove(e, c, headAsset(e.give)), wholeMove(w, e, headAsset(e.want)))'
            new = 'exchange(wholeMove(e, c, headAsset(e.give)), wholeMove(e, c, headAsset(e.give)))'
            assert source.count(old) == 1, 'double-pay plant anchor changed'
            changed = source.replace(old, new)
            assert changed != source and changed.replace(new, old) == source, 'mutation not exact'
            path = self.w.root / 'DoublePay.obend'
            path.write_text(changed)
            bounty['sourcePath'] = str(path)
            evidence = {'name': 'double-pay', 'source': str(path),
                        'before': hashlib.sha256(source.encode()).hexdigest(),
                        'after': hashlib.sha256(changed.encode()).hexdigest()}
            self.mutations.append(evidence)
            self.w.check('plant-double-pay-source-changed', evidence['before'] != evidence['after'], evidence)
        self.publish(name, 'escrow', [self.module('NatOrder', 'world/workshop/NatOrder.obend'), bounty,
            self.module('Escrow', 'world/commission/Escrow.obend',
                        [self.imported('Bounty', './BountyEscrow.obend', 1)])], seat=True)

    def invoke(self, tag, name, method, args, expect='installed', detail=None, grants=None):
        w = self.w
        obj = w.objects[name]
        body = {'kind': 'invoke', 'object': obj['object'], 'objectCapability': obj['capability'],
                'method': method, 'args': args, 'envelope': cap(15000, domain=64),
                'account': w.SPONSOR_ACCOUNT, 'accountCapability': w.SPONSOR_SPEND, 'opId': op_id()}
        if grants is not None:
            body['grants'] = grants
        value = w.turn(tag, w.sponsor, body, expect, detail)
        self.receipts[tag] = value
        return value

    def work(self, units=1, claimant=None):
        return record(units=nat(units), claimant=nat(claimant or self.w.SECOND))

    def grant(self, board, method, limit=1, uses=1):
        return {'object': self.w.objects[board]['object'], 'method': method, 'code': self.pins['Board'],
                'caller': self.w.objects['agent']['object'], 'args': {'cap': {'path': ['units'], 'limit': str(limit)}},
                'uses': str(uses)}

    def fleet(self, tag, board, method, units=1, expect='installed', detail=None, grants=None, twice=False,
              claimant=None):
        route = record(target=nat(self.w.objects[board]['object']), method=label(method),
                       args=self.work(units, claimant))
        return self.invoke(tag, 'agent', 'twice' if twice else 'run', route, expect, detail,
                           grants if grants is not None else [self.grant(board, 'claim'), self.grant(board, 'submit')])

    def state(self, name, tag):
        return self.w.state(name, tag)['state']

    def setup(self):
        w = self.w
        board_fields = ('reward', 'claimant', 'submitted', 'approved', 'cancelled', 'reviewer')
        governed = {'governed': {'authority': eq('request/subject', w.SPONSOR), 'floors': []}}
        w.create('create-guild', w.sponsor, 'guild', eq('request/subject', w.SPONSOR), 'installed',
                 pin=self.pins['Guild'], seed=record(member=nat(w.SECOND), active=nat(1)),
                 state_type=state_type('member', 'active'), upgrade=governed)
        # Reviewer permits only Board callers (plus creation), never the fleet agent.
        review_law = any_of(eq('request/turn', 4),
                           *(eq('request/caller', w.objects[n]['object']) for n in ('happy', 'cancel', 'silence')))
        w.create('create-reviewer', w.sponsor, 'reviewer', review_law, 'installed', pin=self.pins['Review'],
                 seed=record(revision=nat(1), endorsed=nat(1)), state_type=state_type('revision', 'endorsed'))
        w.create('create-agent', w.sponsor, 'agent', eq('request/subject', w.SPONSOR), 'installed',
                 pin=self.pins['Agent'], seed=record(total=nat(0)))
        for name in ('happy', 'cancel', 'silence'):
            w.create('post-' + name, w.sponsor, name, eq('request/subject', w.SPONSOR), 'installed',
                     pin=self.pins['Board'], state_type=state_type(*board_fields), upgrade=governed,
                     seed=record(reward=nat(REWARD), claimant=nat(0), submitted=nat(0), approved=nat(0),
                                 cancelled=nat(0), reviewer=nat(w.objects['reviewer']['object'])))
            law = any_of(eq('member/0/state/claimant', 0),
                         all_of(eq_slots('member/0/state/claimant', 'member/1/state/member'),
                                eq('member/1/state/active', 1)))
            w.turn('register-' + name, w.sponsor, {'kind': 'registerDomain',
                'members': [dict(object=w.objects[n]['object'], capability=w.objects[n]['capability'])
                            for n in (name, 'guild')], 'law': law, 'payer': w.SPONSOR_ACCOUNT,
                'payerCapability': w.SPONSOR_SPEND, 'envelope': cap(0, full=False, domain=64)}, 'installed')
            domains = w.state(name, 'registered-' + name)['objectRecord'].get('domains')
            w.check('board-in-guild-domain-' + name, isinstance(domains, list) and len(domains) == 1, domains)
        domains = w.state('guild', 'guild-domains')['objectRecord'].get('domains')
        w.check('guild-in-all-three-domains', isinstance(domains, list) and len(domains) == 3, domains)
        # Real Book assets, issuer custody, no modeled reward balance.
        w.sh('create-commission-realm', w.mini, 'workspace', '--action', 'create', '--dir', w.sponsor,
             '--name', 'commissions', '--storage', 'declared', '--predicate', w.root / 'permit-all.json')
        for name in ('gold', 'receipt'):
            w.sh('well-' + name, w.mini, 'well', '--action', 'new', '--dir', w.sponsor, '--name', name,
                 '--in', 'commissions', '--law', w.root / 'permit-all.json')
        self.gold, self.receipt = [json.loads((w.sponsor / 'refs' / f'{n}.json').read_text())['target']
                                   for n in ('gold', 'receipt')]
        self.mint('gold', w.SPONSOR_ACCOUNT, 400)
        self.seat_view('initial')

    def mint(self, asset, account, amount):
        w = self.w
        w.sh(f'mint-{asset}-{account}-{amount}', w.mini, 'well', '--action', 'mint', '--dir', w.sponsor,
             '--well', asset, '--account', account, '--amount', amount)

    def seat_turn(self, tag, body, expect='installed', detail=None, workspace=None, object_cap=None,
                  account_cap=None):
        w = self.w
        command = w.root / f'{tag}.seat.json'
        document = {'turn': body}
        if body.get('kind') == 'offer' and body['proposal'].get('donate'):
            document['confirmDonation'] = True
        if object_cap is not None:
            document['objectCapability'] = object_cap
        if account_cap is not None:
            document['accountCapability'] = account_cap
        command.write_text(json.dumps(document))
        value = w.last_json(w.sh(tag, w.mini, 'seat', '--action', 'submit', '--workspace', workspace or w.sponsor,
                                  '--command', command, '--out', w.attempts / tag, ok=(0, 1, 2)))
        self.receipts[tag] = value
        return w.judge(tag, value, expect, detail)

    def seat_view(self, tag):
        w = self.w
        request = {'seats': self.seats, 'accounts': [w.SPONSOR_ACCOUNT, w.SECOND, self.gold, self.receipt] + self.seats,
                   'assets': [self.gold, self.receipt]}
        view = w.last_json(w.sh('seat-view-' + tag, w.mini, 'seat', '--action', 'view', '--workspace', w.sponsor,
                                '--request', json.dumps(request)))
        total = next(t['total'] for t in view['totals'] if t['asset'] == self.gold)
        self.gold_totals.append({'after': tag, 'total': total})
        return view

    def height(self):
        return int(self.w.view('height', {})['height'])

    def seat_invoke(self, tag, instance, inp, expect='installed', detail=None):
        w = self.w
        envelope = {k: '0' for k in MAXIMUM}
        for k in ('heap', 'stack', 'typeFuel', 'outputNodes', 'outputBytes', 'extractTicks'):
            envelope[k] = str(MAXIMUM[k])
        envelope['sourceTicks'] = '150000'
        return self.seat_turn(tag, {'kind': 'invoke', 'instance': w.objects[instance]['object'],
             'input': inp, 'envelope': envelope, 'account': w.SPONSOR_ACCOUNT}, expect, detail,
             object_cap=w.objects[instance]['capability'], account_cap=w.SPONSOR_SPEND)

    def offer(self, tag, instance, pin, invitation, role, give=(), want=(), deadline=None, second=False):
        w = self.w
        proposal = {'give': [{'asset': asset, 'amount': str(n)} for asset, n in give],
                    'want': [{'asset': asset, 'amount': str(n)} for asset, n in want]}
        if deadline is not None:
            proposal['afterDeadline'] = str(deadline)
        if not want:
            proposal['donate'] = True
        account = w.SECOND if second else w.SPONSOR_ACCOUNT
        value = self.seat_turn(tag, {'kind': 'offer', 'invitation': invitation,
              'expect': {'instance': w.objects[instance]['object'], 'package': pin, 'role': role},
              'funding': account, 'payee': account, 'proposal': proposal, 'holder': None},
              workspace=w.second if second else w.sponsor,
              account_cap=w.SECOND_SPEND if second else w.SPONSOR_SPEND)
        seat = value['seatAccount']
        self.seats.append(seat)
        return seat

    def invitations(self, tag, ids, instance, pin, roles, holder):
        # Host.SeatJson.commandJson returns eight PREDICTED ids for any invoke.
        # Judge the actual stored invitations, not the prediction array length.
        w = self.w
        view = w.last_json(w.sh('invitations-' + tag, w.mini, 'seat', '--action', 'view',
                               '--workspace', w.sponsor, '--request', json.dumps({'invitations': ids})))
        actual = {c['invitation']['id']: c['invitation'] for c in view['cells'] if c.get('kind') == 'invitation'}
        expected = dict(zip(ids, roles))
        exact = len(expected) == len(roles) and set(actual) == set(expected) and all(
            actual[i]['role'] == role and actual[i]['holder'] == holder and not actual[i]['spent'] and
            actual[i]['instance'] == w.objects[instance]['object'] and actual[i]['package'] == pin
            for i, role in expected.items())
        w.check(tag, exact, actual)

    def escrow(self, name, pin=None):
        w = self.w
        pin = pin or self.pins['Escrow']
        instance = name + '-escrow'
        self.seat_turn(name + '-escrow-create', {'kind': 'create', 'instance': w.objects[instance]['object'],
                       'pin': pin, 'clause': PERMIT_ALL}, object_cap=w.objects[instance]['capability'])
        ids = self.seat_invoke(name + '-invitations', instance,
                              variant('post', record(holder=nat(w.SPONSOR), review=nat(3))))['mintIds']
        self.invitations(name + '-four-invitations', ids, instance, pin,
                         ['escrow', 'approve', 'reject', 'cancel'], w.SPONSOR)
        before = balances(self.seat_view(name + '-before-funding'))
        escrow = self.offer(name + '-fund', instance, pin, ids[0], 'escrow',
                            [(self.gold, REWARD)], [(self.receipt, 1)], self.height() + 120)
        after = balances(self.seat_view(name + '-funded'))
        w.check(name + '-reward-held', after[(escrow, self.gold)] == REWARD and
                before[(w.SPONSOR_ACCOUNT, self.gold)] - after[(w.SPONSOR_ACCOUNT, self.gold)] == REWARD,
                {'seat': after[(escrow, self.gold)]})
        return {'name': name, 'instance': instance, 'pin': pin, 'escrow': escrow,
                'approve': ids[1], 'cancel': ids[3]}

    def claim_seat(self, escrow):
        w = self.w
        name, instance, pin = escrow['name'], escrow['instance'], escrow['pin']
        ids = self.seat_invoke(name + '-claim-invitations', instance,
                              variant('claim', record(holder=nat(w.SECOND))))['mintIds']
        self.invitations(name + '-paired-invitations', ids, instance, pin, ['claim', 'work'], w.SECOND)
        due = self.height() + 24
        escrow['claim'] = self.offer(name + '-claim-seat', instance, pin, ids[0], 'claim',
                                    want=[(self.gold, REWARD)], deadline=due, second=True)
        escrow['work_invitation'], escrow['due'] = ids[1], due

    def submit_seat(self, escrow, expect='installed', detail=None):
        name, instance, pin = escrow['name'], escrow['instance'], escrow['pin']
        self.mint('receipt', self.w.SECOND, 1)
        escrow['work'] = self.offer(name + '-work-seat', instance, pin, escrow['work_invitation'], 'work',
                                   give=[(self.receipt, 1)], second=True)
        return self.seat_invoke(name + '-exchange', instance, variant('advance', record()), expect, detail)

    def exit(self, tag, seat, expect='installed', detail=None):
        return self.seat_turn(tag, {'kind': 'exit', 'seat': seat}, expect, detail, workspace=self.w.second)

    def happy(self):
        w = self.w
        listing = self.invoke('CB1-list', 'happy', 'list', self.work())['report']
        w.check('CB1-list-posted-reward', field(listing, 'reward') == nat(REWARD), listing)
        before = self.state('happy', 'before-reward-change')
        self.invoke('CB1-reward-write-refused', 'happy', 'reviseReward', self.work(REWARD + 1),
                    'charged', ['lawDenied', 'writeOnce', 'reward'])
        w.check('CB1-reward-kept', self.state('happy', 'reward-kept') == before, before)
        e = self.escrow('happy')
        grants = [self.grant('happy', 'claim'), self.grant('happy', 'submit')]
        self.fleet('CB1-over-cap', 'happy', 'claim', units=2, expect='charged', detail=['grantMismatch', 'cap'])
        self.fleet('CB1-other-board', 'cancel', 'claim', expect='charged', detail='lawDenied', grants=grants)
        self.fleet('CB1-other-method', 'happy', 'cancel', expect='charged', detail='lawDenied', grants=grants)
        self.fleet('CB1-nonmember', 'happy', 'claim', claimant=41, expect='charged', detail='domainLawDenied')
        self.fleet('CB1-cumulative-cap', 'happy', 'claim', expect='charged', detail=['grantMismatch', 'cap'],
                   grants=[self.grant('happy', 'claim', uses=2)], twice=True)
        w.check('CB1-refusals-kept-board', self.state('happy', 'before-claim') == before, None)
        self.fleet('CB1-agent-claim', 'happy', 'claim')
        self.claim_seat(e)
        self.invoke('CB1-guild-deactivate-refused', 'guild', 'deactivate', self.work(), 'charged', 'domainLawDenied')
        self.fleet('CB1-agent-submit', 'happy', 'submit')
        self.submit_seat(e)
        submitted = balances(self.seat_view('CB1-submitted'))
        w.check('CB1-reward-for-receipt', submitted[(e['claim'], self.gold)] == REWARD and
                submitted[(e['escrow'], self.receipt)] == 1 and submitted[(e['escrow'], self.gold)] == 0, submitted_to_json(submitted))
        self.exit('CB1-early-exit-refused', e['claim'], 'refused', 'exitNotAuthorized')
        # A stale serial returns zero from CatalogReview, then the exact work is approved.
        stale = self.invoke('CB1-review-stale', 'happy', 'review', self.work(2))
        w.check('CB1-stale-review-held', stale.get('report') == nat(0), stale.get('report'))
        approval = self.invoke('CB1-review-call', 'happy', 'review', self.work())
        w.check('CB1-review-approved', approval.get('report') == nat(1), approval.get('report'))
        # The poster consumes its own approval invitation after observing that call.
        if approval.get('report') != nat(1):
            raise RuntimeError('review did not approve; no approval seat may be offered')
        self.offer('CB1-approval-seat', e['instance'], e['pin'], e['approve'], 'approve')
        pre = balances(self.seat_view('CB1-before-pay'))
        self.seat_invoke('CB1-pay', e['instance'], variant('advance', record()))
        paid = balances(self.seat_view('CB1-paid'))
        w.check('CB1-paid-once', paid[(w.SECOND, self.gold)] - pre[(w.SECOND, self.gold)] == REWARD, None)
        w.check('CB1-poster-received-work', paid[(w.SPONSOR_ACCOUNT, self.receipt)] -
                pre[(w.SPONSOR_ACCOUNT, self.receipt)] == 1, None)
        self.exit('CB1-second-pay-refused', e['claim'], 'refused', 'seatMissing')
        again = balances(self.seat_view('CB1-no-second-pay'))
        w.check('CB1-no-second-payment', again[(w.SECOND, self.gold)] == paid[(w.SECOND, self.gold)], None)

    def cancellation(self):
        w = self.w
        pre = balances(self.seat_view('CB5-before-post'))
        e = self.escrow('cancel')
        self.invoke('CB5-cancel-unclaimed', 'cancel', 'cancel', self.work())
        self.offer('CB5-cancel-seat', e['instance'], e['pin'], e['cancel'], 'cancel')
        self.seat_invoke('CB5-refund', e['instance'], variant('advance', record()))
        refunded = balances(self.seat_view('CB5-refunded'))
        w.check('CB5-poster-refunded', refunded[(w.SPONSOR_ACCOUNT, self.gold)] ==
                pre[(w.SPONSOR_ACCOUNT, self.gold)], None)
        self.fleet('CB5-cancelled-board-no-claim', 'cancel', 'claim', expect='charged', detail=['lawDenied', 'cancelled'])
        # An active claimed commission (not yet submitted) must also refuse cancellation.
        self.silent_escrow = self.escrow('silence')
        self.fleet('CB5-active-claim', 'silence', 'claim')
        self.claim_seat(self.silent_escrow)
        before = self.state('silence', 'CB5-before-cancel')
        funds = balances(self.seat_view('CB5-before-refusal'))
        self.invoke('CB5-cancel-after-claim-refused', 'silence', 'cancel', self.work(),
                    'charged', ['lawDenied', 'cancelled', 'claimant'])
        w.check('CB5-claimed-state-kept', self.state('silence', 'CB5-after-cancel') == before, None)
        after = balances(self.seat_view('CB5-after-refusal'))
        w.check('CB5-no-refund-after-claim', after == funds, None)

    def silence(self):
        w = self.w
        e = self.silent_escrow
        self.fleet('CB7-agent-submit', 'silence', 'submit')
        self.submit_seat(e)
        pre = balances(self.seat_view('CB7-submitted'))
        w.check('CB7-no-review', field(self.state('silence', 'CB7-board'), 'approved') == nat(0), None)
        self.exit('CB7-before-deadline', e['claim'], 'refused', 'exitNotAuthorized')
        for n in range(40):
            if self.height() >= e['due']:
                break
            self.seat_invoke(f'CB7-height-{n}', e['instance'], variant('pad', record(holder=nat(w.SPONSOR))))
        w.check('CB7-deadline-reached', self.height() >= e['due'], e['due'])
        self.exit('CB7-silence-pays', e['claim'])
        paid = balances(self.seat_view('CB7-paid'))
        w.check('CB7-claimant-paid', paid[(w.SECOND, self.gold)] - pre[(w.SECOND, self.gold)] == REWARD, None)
        self.exit('CB7-paid-once', e['claim'], 'refused', 'seatMissing')

    def double_pay(self):
        w = self.w
        e = self.escrow('plant', self.pins['DoublePay'])
        self.claim_seat(e)
        # Capture the roots AFTER the work offer but BEFORE the bad reallocation.
        self.mint('receipt', w.SECOND, 1)
        e['work'] = self.offer('plant-work-seat', e['instance'], e['pin'], e['work_invitation'], 'work',
                               give=[(self.receipt, 1)], second=True)
        pre = self.seat_view('plant-before')
        self.seat_invoke('CBP-double-pay-refused', e['instance'], variant('advance', record()), 'refused', 'unfunded')
        post = self.seat_view('plant-after')
        roots = lambda v: {c['cell']: c['root'] for c in v.get('cells', [])}
        w.check('CBP-roots-unchanged', roots(pre) == roots(post), None)
        w.check('CBP-balances-unchanged', balances(pre) == balances(post), None)
        w.check('CBP-reward-still-held', balances(post)[(e['escrow'], self.gold)] == REWARD, None)


def submitted_to_json(b):
    return {account + '/' + asset: value for (account, asset), value in b.items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bin', required=True)
    parser.add_argument('--root', required=True)
    parser.add_argument('--plant', choices=['double-pay'])
    args = parser.parse_args()
    required = ('minidregg-host', 'mini', 'minidregg-link-sqlite-store', 'minidregg-credential-signature-verifier')
    missing = [name for name in required if not (pathlib.Path(args.bin) / name).is_file()]
    if missing:
        print('UNCONFIGURED missing inputs: ' + ', '.join(missing), file=sys.stderr)
        return 98
    w = World(args.bin, args.root, REPO)
    app = Commission(w)
    try:
        with w.group('CB0-packages-and-guild'):
            w.bring_up(['happy', 'cancel', 'silence', 'agent', 'reviewer', 'guild',
                        'happy-escrow', 'cancel-escrow', 'silence-escrow', 'plant-escrow'])
            app.packages(planted=True)
            app.setup()
        if any(not row['ok'] for row in w.results):
            raise RuntimeError('setup failed; required package/domain admission did not complete')
        with w.group('CB1-happy'):
            app.happy()
        with w.group('CB5-cancellation'):
            app.cancellation()
        with w.group('CB7-silence'):
            app.silence()
        with w.group('CBP-double-pay'):
            app.double_pay()
        with w.group('CB-book-conservation'):
            totals = {str(row['total']) for row in app.gold_totals}
            w.check('Book-gold-total-unchanged', len(totals) == 1 and len(app.gold_totals) > 10, sorted(totals))
    except Exception as error:
        traceback.print_exc()
        w.check('journey-completed', False, str(error))
    finally:
        if hasattr(w, 'W'):
            w.stop()
    (w.root / 'receipts.json').write_text(json.dumps(app.receipts, indent=1) + '\n')
    return w.finish({'pins': app.pins, 'goldTotals': app.gold_totals, 'mutations': app.mutations,
                     'plant': args.plant, 'guildMembership': 'permanent'})


if __name__ == '__main__':
    sys.exit(main())
