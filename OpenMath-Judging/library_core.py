"""Offline file catalogue. Reads archives and text; never imports entrant code."""
import pathlib, hashlib, zipfile, re, sqlite3

CATEGORIES = {
    '01-submission': 'Submission and claims',
    '02-papers': 'Papers and explanations',
    '03-novelty': 'Novelty and prior work',
    '04-formal-proofs': 'Lean and formal proofs',
    '05-certificates': 'Certificates and constructions',
    '06-data': 'Results and data',
    '07-reproduction': 'Verification and reproduction',
    '08-logs': 'Logs and experiments',
    '09-team': 'Team, rights and provenance',
    '10-build': 'Dependencies and build configuration',
    '11-other': 'Other supporting files',
    '12-correspondence': 'Source messages and receipts',
    '13-archives': 'Original archives',
}
TOPICS = ['General / shared', 'Ramsey multiplicity', 'Matrix multiplication', 'Kobon triangles', 'Collatz', 'Busy Beaver', 'Grothendieck / CHSH', 'Erdos 3', 'Cerny', 'Heilbronn', 'DMS / graph colouring', 'Other formal mathematics']

def classify(path):
    p = path.lower().replace('\\', '/'); name = p.rsplit('/', 1)[-1]; ext = pathlib.PurePosixPath(p).suffix
    if '/correspondence/' in p or name.startswith(('email-', 'linkedin-', 'whatsapp-', 'hill-result-')): key='12-correspondence'
    elif ext in ('.zip', '.7z', '.tar', '.gz', '.bundle'): key='13-archives'
    elif p.startswith('.lake/') or '/.lake/' in p or '/node_modules/' in p or '/site-packages/' in p: key='10-build'
    elif ext in ('.lean', '.v', '.thy', '.agda', '.dfy') and name != 'lakefile.lean': key='04-formal-proofs'
    elif any(s in name for s in ('novelty', 'prior_work', 'prior-work', 'motivation', 'bibliograph', 'related_work', 'related-work', 'references')) or ext=='.bib': key='03-novelty'
    elif any(s in name for s in ('license', 'notice', 'rights', 'author', 'credit', 'team', 'provenance', 'attribution')): key='09-team'
    elif any(s in name for s in ('submission', 'completion', 'claim', 'scope', 'packet', 'final-summary')) and ext in ('.md', '.txt', '.json', '.yaml', '.yml', '.csv'): key='01-submission'
    elif any(s in p for s in ('reproduce', 'reproduction', 'verify', 'verifier', 'checker', 'check_', 'validation', 'audit', '/tests/')) and ext not in ('.log',): key='07-reproduction'
    elif any(s in name for s in ('certificate', 'witness', 'solution', 'construction', 'arrangement', 'exact_graph', 'exact-graph', 'machine')) and ext in ('.json', '.txt', '.csv', '.npy', '.npz', '.cnf', '.drat', '.lrat', '.dimacs', '.pkl', '.smt2', '.md'): key='05-certificates'
    elif any(s in p for s in ('/paper/', '/papers/', '/manuscript', '/article', '/exposition')) or ext in ('.pdf', '.tex', '.docx', '.pptx', '.ipynb'): key='02-papers'
    elif ext in ('.log', '.out', '.err') or any(s in p for s in ('/logs/', '/experiments/', '/runs/')): key='08-logs'
    elif name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean', 'requirements.txt', 'pyproject.toml', 'package.json', 'package-lock.json', 'cargo.toml', 'makefile', 'dockerfile', '.gitignore', '.gitmodules') or p.startswith(('.github/', '.lake/')) or '/.lake/' in p or ext in ('.olean', '.ilean', '.o', '.dll', '.exe', '.so', '.pyc'): key='10-build'
    elif ext in ('.csv', '.tsv', '.json', '.jsonl', '.npy', '.npz', '.txt', '.cnf', '.drat', '.lrat', '.sqlite', '.db', '.png', '.jpg', '.svg', '.mp4', '.wav', '.bin', '.dat'): key='06-data'
    elif ext in ('.py', '.c', '.cpp', '.h', '.sh', '.ps1', '.jl', '.rs', '.sage', '.m', '.js', '.ts', '.toml', '.yml', '.yaml'): key='07-reproduction'
    elif name.startswith('readme') or ext in ('.md', '.rst'): key='02-papers'
    else: key='11-other'
    topic='General / shared'
    for needles, label in [
        (('heilbronn',), 'Heilbronn'), (('ramsey', 'clique-cluster', 'ramtastic'), 'Ramsey multiplicity'),
        (('kobon', 'triangle', 'k18', 'n39'), 'Kobon triangles'),
        (('collatz', 'modular-descent'), 'Collatz'), (('busybeaver', 'busy-beaver', 'busy_beaver', 'bb6', '/bb/'), 'Busy Beaver'),
        (('grothendieck', 'chsh'), 'Grothendieck / CHSH'), (('matrix-multiplication', 'matrix_multiplication', 'brent', 'laderman', 'smirnov'), 'Matrix multiplication'),
        (('erdos-3', 'erdos_3', 'erdos3', 'harmonic', 'reciprocal'), 'Erdos 3'),
        (('cerny', 'synchronizing'), 'Cerny'), (('dms', 'star-edge', 'star_edge', 'cubic16'), 'DMS / graph colouring'),
        (('/m2/', 'erdos', 'hypergraph', 'campossamotij', 'quaternion'), 'Other formal mathematics')]:
        if any(n in p for n in needles): topic=label; break
    return key, topic, 'Filename/path inference; editable in the app'

def connect(root):
    c=sqlite3.connect(pathlib.Path(root)/'catalogue.sqlite'); c.row_factory=sqlite3.Row; c.execute('PRAGMA foreign_keys=ON'); return c

def read_bytes(root, row, limit=None):
    if row['local_path']:
        with (pathlib.Path(root)/row['local_path']).open('rb') as f: return f.read() if limit is None else f.read(limit)
    with zipfile.ZipFile(pathlib.Path(root)/row['archive_path']) as z:
        with z.open(row['archive_member']) as f: return f.read() if limit is None else f.read(limit)

def materialize(root, row):
    root=pathlib.Path(root).resolve()
    if row['local_path']: return root/row['local_path']
    # Opaque file id and sanitized basename prevent traversal, collisions and reserved filenames.
    name=re.sub(r'[^\w. -]', '_', pathlib.PurePosixPath(row['original_path']).name)[:100] or 'file'
    if name.rstrip('. ').split('.')[0].upper() in {'CON','PRN','AUX','NUL',*[f'COM{i}' for i in range(1,10)],*[f'LPT{i}' for i in range(1,10)]}: name='file-'+name
    dest=root/'contestants'/row['team_id']/row['category']/'opened-files'/(str(row['id'])+'-'+name)
    dest.parent.mkdir(parents=True,exist_ok=True)
    if not dest.exists():
        data=read_bytes(root,row)
        if row['sha256'] and hashlib.sha256(data).hexdigest()!=row['sha256']: raise ValueError('File hash mismatch')
        dest.write_bytes(data)
    return dest
