"""Preserve a metadata-only ambiguous-suffix projection and bind its exact-path correction."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil
from resource_metrics import snapshot
BASE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
old=BASE/'htpeo-ramsey2056-measured-output-storage-time-projection-20261005.json'
oldsha='362b034df050b44a3ed88a41057b561fea15bc6d28bea73735dd5d9b860004e8'
packet=BASE/'htpeo-ramsey2056-granular-continuation-preparation-20261005.json'
packetsha='5fe7ba9f9ac0092195b7090a0e8f133e1132073f4e0a38153c69e110c11c4956'
assert sha(old)==oldsha and sha(packet)==packetsha
doc=json.loads(old.read_bytes());newpacket=json.loads(packet.read_bytes())
target=(BASE/'builds/htpeo-ramsey-current/RamseyCert/Chunk/B0.olean').resolve()
exact=[a for a in doc['all36_current_output_native_identity'] if Path(a['file']).resolve()==target]
assert len(exact)==1;out=exact[0]
assert out['bytes']==900496 and out['sha256']=='02f47c4a043a6931357bd3b224f44064697224a744eff3276090617a641d3825'
assert out['native']['standard_allocation_bytes']==352256
resources={'disk_free_bytes':shutil.disk_usage(BASE).free,**snapshot()}
doc.update(status='READ_ONLY_CORRECTED_EXACT_B0_SINGLE_CHUNK_SCENARIOS_NOT_UPPER_BOUNDS',
 corrected_utc=datetime.now(timezone.utc).isoformat(),producer_sha256=sha(__file__),
 preserved_prior_projection=str(old),preserved_prior_projection_sha256=oldsha,
 metadata_error='The prior projection selected Data.EntB0 using an ambiguous suffix. This correction selects the sole exact RamseyCert/Chunk/B0.olean path. Source scope, adapter and scientific artifacts were never changed.',
 first_kernel_output_current_native=out,current_resources=resources)
doc['scenario_if_each_remaining_chunk_equals_B0']={'kernel_seconds':2047*doc['first_kernel_chunk_actual']['seconds'],
 'kernel_hours':2047*doc['first_kernel_chunk_actual']['seconds']/3600,
 'kernel_output_logical_bytes':2047*out['bytes'],'kernel_output_allocated_bytes':2047*out['native']['standard_allocation_bytes'],
 'estimated_disk_free_after_kernel_only':resources['disk_free_bytes']-2047*out['native']['standard_allocation_bytes']}
doc['scenario_if_every_chunk_is_twice_B0_allocated']={'kernel_output_allocated_bytes':2047*2*out['native']['standard_allocation_bytes'],
 'estimated_disk_free_after_kernel_only':resources['disk_free_bytes']-2047*2*out['native']['standard_allocation_bytes']}
destination=BASE/'htpeo-ramsey2056-exactB0-corrected-measured-output-storage-time-projection-20261005.json'
with destination.open('x',encoding='utf8',newline='\n') as f:json.dump(doc,f,indent=2);f.write('\n')
newpacket.update(status='PREPARED_ONLY_CORRECTED_EXACT_B0_PROJECTION_ROOT_REVIEW_REQUIRED_NO_DISPATCH',
 projection=str(destination),projection_sha256=sha(destination),
 preserved_prior_packet=str(packet),preserved_prior_packet_sha256=packetsha,
 correction_producer=str(Path(__file__).resolve()),correction_producer_sha256=sha(__file__))
newdestination=BASE/'htpeo-ramsey2056-granular-continuation-corrected-preparation-20261005.json'
with newdestination.open('x',encoding='utf8',newline='\n') as f:json.dump(newpacket,f,indent=2);f.write('\n')
print(json.dumps({'corrected_projection':str(destination),'corrected_projection_sha256':sha(destination),
 'corrected_packet':str(newdestination),'corrected_packet_sha256':sha(newdestination),
 'scenario':doc['scenario_if_each_remaining_chunk_equals_B0'],'mutations_to_science_or_storage':0},indent=2))
