from pathlib import Path
import json,re
root=Path(__file__).resolve().parent
inventory=json.loads((root/'OpenMath-complete-team-inventory.json').read_text(encoding='utf-8'))
todo_path=Path('[LOCAL PRIVATE OBLIGATIONS RECORD]')
todo=todo_path.read_text(encoding='utf-8-sig')
todo=re.sub(r'^- W22 \|.*$', '- W22 | Luca / Mateus / Ueverton / organizers | Final Leanification named rosters and credits | NEW: Luca October 2 23:09 CEST reports five contributors; Ueverton earlier reported two registered teams. Handbook limit is four. Obtain named roster and chair decision, preserving real authorship and avoiding duplicate credit. | Before scoring. | Organizer/roster clarification required',todo,flags=re.M)
todo+='\nInventory coverage addendum: Autolab list rechecked: seven hills, 111 climbs; list Discussion has zero comments. Sundai Pitch is login-gated, so no unpublished pitch participants are inferred. The 42 account identities come from the captured successful-run tables, not all private/unscored climbs.\n'
todo_path.write_text(todo,encoding='utf-8-sig')
old=root/'OpenMath-follow-up-drafts-UNSENT.txt'
text=old.read_text(encoding='utf-8-sig')
warning='SUPERSEDED: use OpenMath-all-team-drafts-UNSENT.txt. New Luca email reports five contributors and contradicts earlier two-team framing; use combined Leanification roster message. No original drafts sent.\n\n'
if not text.startswith('SUPERSEDED:'): old.write_text(warning+text,encoding='utf-8-sig')
for name in ['OpenMath-team-status.html','obligations-current.html']:
    p=root/name;content=p.read_text(encoding='utf-8')
    banner='<p style="padding:16px;background:#fff2cc"><b>Updated inventory and drafts:</b> <a href="OpenMath-complete-team-inventory.html">Open the full roster, individual messages and rationale</a>. New Luca email reports five Leanification contributors; named rosters and the four-person entrant rule need organizer reconciliation.</p>'
    if 'New Luca email reports five' not in content:content=content.replace('<main>','<main>'+banner,1)
    p.write_text(content,encoding='utf-8')
print(json.dumps({'records':len(inventory['entries']),'draft_lines_max':max(len(e['lines']) for e in inventory['entries']),'all_unsent':all(not e['sent'] for e in inventory['entries']),'roster_records':len(json.loads((root/'OpenMath-Luma-roster.json').read_text(encoding='utf-8')))}))
