import json
from pathlib import Path

root = Path(__file__).resolve().parent
def read(name):
    return json.loads((root / name).read_text(encoding='utf-8-sig'))
def write(name, value):
    (root / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

d = read('obligations-current-data.json')
t = read('OpenMath-team-status.json')
r = read('OpenMath-outreach-final-receipts.json')
drafts = read('OpenMath-additional-candidate-drafts-UNSENT.json')
accounts = read('OpenMath-additional-hill-account-assessment.json')
stamp = r['updated']
report = 'OpenMath-next-messages-and-account-audit.html'
d['ordered'][0] = ['1', 'Immediate / before October 3 06:00 CEST cutoff', 'Review the UNSENT new-candidate and hill-account drafts', 'Fifteen group follow-ups and six interest enquiries SENT/verified; six pending registrations approved. Eighteen additional registered-candidate drafts remain UNSENT. All 33 additional hill accounts assessed; prioritize hl728, danamouk, n0rang2, Rohith, Nikolay/vyahhi and Octavian. Resolve aliases and group overlaps before further sends; await current group replies rather than repeating messages.', report]
for w in d['waiting']:
    if w[0] == 'W20':
        w[:] = ['W20', 'Tom / Edward / Sri / Arham / Alexandros / Martin', 'Responses to six interest-only enquiries', 'Each was asked whether they produced any OpenMath work; all six messages SENT/verified October 2 late evening CEST. No entry commitment or finished result established.', 'Await replies; do not repeat automatically.', 'Interest enquiries complete; responses pending']
    elif w[0] == 'W21':
        w[:] = ['W21', 'Chandragupt / judges / organizers', 'Final revision/receipt and independent mathematical review', 'Invitation received October 2 23:14 CEST and accepted; private repository, paper and novelty documents readable. Source commit c9a07daa149509c7fcddcd13819f5196beed2123. Exact 729-coefficient checks and Lean validity/support claims present but not independently executed.', 'Confirm frozen revision and final receipt; independently check arithmetic and prior-scheme equivalence. Stephen reviewer account still unconfirmed.', 'Repository access DONE; downstream judging pending']
for i, closed in enumerate(d['closed']):
    if closed.startswith('Chandragupt GitHub access reply:'):
        d['closed'][i] = 'Chandragupt access reply/follow-up SENT/verified; invitation accepted and private repository, paper and novelty documents read. Final revision/receipt and independent review remain future work.'
    elif closed.startswith('Ten approved OpenMath outreach messages:'):
        d['closed'][i] = 'Ten initial OpenMath outreach messages were sent/verified previously. The later fifteen team follow-ups and six interest enquiries are now SENT/verified; six pending Luma registrations approved/Going. Eighteen additional-candidate drafts and new account outreach remain UNSENT. Artem’s no-tools WhatsApp reply was sent previously.'
d['follow_up_drafts'] = {
    'file': str(root / 'OpenMath-additional-candidate-drafts-UNSENT.json'),
    'status': '18 additional registered-candidate drafts UNSENT — user review pending; 15 authorized team follow-ups and 6 interest enquiries SENT/verified',
    'account_assessment_file': str(root / 'OpenMath-additional-hill-account-assessment.json'),
    'counts': {'identified_work_contact_groups': 15, 'additional_registered_candidates': 18, 'leaderboard_accounts': 42, 'additional_assessed_accounts': 33, 'interested_outreach_only': 6, 'verified_messages_this_follow_up': 21, 'new_candidate_drafts_unsent': 18},
    'not_unique_team_count': True
}
materials = 'Private GitHub invitation accepted; repository, paper/novelty Markdown and PDF/DOCX exports accessible. Latest visible commit c9a07daa149509c7fcddcd13819f5196beed2123; exact solutions, verification source, Lean and reproduction materials present.'
missing = 'Independent verification of all 729 Brent identities and claimed Lean validity/support coverage; support/arithmetic-cost definitions, prior-scheme equivalence and novelty review; confirm final revision and official receipt. Latest author checks were still running. Stephen reviewer account remains unconfirmed. Repository access and paper delivery are complete.'
for team in t['teams']:
    if team['name'] == 'Chandragupt Sharma':
        team['materials'] = materials
        team['missing'] = missing
        team['review_priority'] = 'High: packet now reviewable; independent mathematical review and final receipt pending'
        team['sources'] = ['https://github.com/ChandraguptSharma07/matrix-multiplication-tensor-3x3', 'Chandragupt-packet-readme-private.txt', 'Chandragupt-paper-visible-private.txt', 'OpenMath-outreach-final-receipts.json']
    if team['name'].startswith('Rachel Teo'):
        team['result'] = team['result'].replace('30140932308', '30140930507')
    if team['name'].startswith('Luca'):
        for entry in d['entrants']:
            if entry[0].startswith('Luca'):
                entry[3] = team['result'] + ' Remaining: ' + team['missing']
for entry in d['entrants']:
    if entry[0] == 'Chandragupt Sharma':
        entry[1] = materials
        entry[2] = 'https://github.com/ChandraguptSharma07/matrix-multiplication-tensor-3x3'
        entry[3] = 'Rank-23 support-138 construction; not rank 22. Remaining: ' + missing
    if entry[0].startswith('Rachel Teo'):
        entry[3] = entry[3].replace('30140932308', '30140930507')
t['coverage'] = ['CURRENT OUTREACH UPDATE ' + stamp + ': All fifteen authorized group follow-ups and six interest enquiries SENT/verified. Six pending Luma registrations approved; current table 30 Going/1 Not Going. Eighteen additional-candidate drafts remain UNSENT for review; all 33 additional hill accounts assessed. Chandragupt private packet accessible. Authenticated Sundai pitch queue read and no additional teams identified. Fresh leaderboards and account profiles reviewed; no contestant code independently executed. Latest report: ' + report] + ['HISTORICAL INITIAL AUDIT — ' + line for line in t['coverage']]
write('obligations-current-data.json', d)
write('OpenMath-team-status.json', t)
ids = [item['id'] for item in r['receipts']]
assert len(ids) == len(set(ids)) == 21
assert set(f'E{i:02d}' for i in range(1, 16)).issubset(ids)
assert set(f'E{i:02d}' for i in range(67, 73)).issubset(ids)
assert all(item.get('sent') is True for item in r['receipts'])
assert len(drafts['drafts']) == 18
assert len(accounts['accounts']) == 33
assert len(r['registrations_approved']) == 6
print('Verified: 21 distinct SENT receipts, all E01–E15 and E67–E72; six approvals; 18 review drafts; 33 account assessments. Structured continuity synchronized.')
