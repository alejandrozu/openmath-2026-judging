from pathlib import Path
import json,hashlib
from exact_kobon_geometry import count
here=Path(__file__).resolve().parent
path=here/'rohith_n61_1190_source.json'
expected='f5f7a7ee4f8d55c10c669ffc7622eb15eead1427035214b93e885bd65bc95d7f'
assert hashlib.sha256(path.read_bytes()).hexdigest()==expected
data=json.loads(path.read_text(encoding='utf8'))
rows=data.get('lines_frac',data.get('lines'))
assert rows is not None, list(data)
result=count(rows)
assert result['lines']==61 and result['triangular_faces']==1190
assert result['parallel_pairs']==0 and result['distinct_vertices']==1830 and result['simple']
out={'scope':'Exact rational straight-line geometry only; no Lean replay or historical novelty conclusion',
     'source':'https://raw.githubusercontent.com/Rohith18p/rsi-kobon-triangles/f462d8e18aea2a458376c523c9b6c2980237071f/kobon-triangles/bases/n61_1190_base31.json',
     'source_sha256':expected,'result':result,'all_pass':True}
(here/'rohith_k61_geometry_receipt.json').write_text(json.dumps(out,indent=2),encoding='utf8')
print(json.dumps(out,indent=2))
