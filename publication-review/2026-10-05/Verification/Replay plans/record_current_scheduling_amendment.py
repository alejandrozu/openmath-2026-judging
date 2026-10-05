"""Record the reviewed three-importer lease; does not launch any work."""
from pathlib import Path
from datetime import datetime, timezone
import json, os, shutil
from resource_metrics import snapshot

base=Path(__file__).resolve().parent
result={
    'recorded_utc':datetime.now(timezone.utc).isoformat(),
    'status':'ROOT_REVIEWED_CONDITIONAL_DISPATCH_LEASE',
    'maximum_total_source_importers':3,
    'maximum_literal_whole_Mathlib_importers':1,
    'allowed_concurrent_scopes':['Luke unchanged native Count pilot',
                                 'one granular E829 / E3 with pullback / OPDP89 scope',
                                 'Matt first authored source pilot and, if measured PASS, its 26-source scope'],
    'held_scopes':['DMS dispatcher at a genuine completed-source boundary',
                   'E169 whole-Mathlib retry', 'A000 remaining sources',
                   'Luke remaining-source continuation before Count/RawCount review'],
    'basis':{'Count_authored_literal_whole_Mathlib_imports':0,
             'Count_observed_private_bytes':3144503296,
             'Count_observation_utc':'2026-10-05T01:14:39Z',
             'Matt_prior_full_Mathlib_import_pilot_status':'PASS',
             'Matt_prior_full_import_peak_private_bytes':890810368},
    'policy':'No dispatch or continuous reserve floor is reduced. An unavailable dispatch gate is a no-attempt resource hold, not a proof failure. Preserve all original receipts and source bytes.',
    'Count_and_RawCount_policy':'The conservative 10 GiB own and 11 GiB available-commit dispatch policy remains unchanged. RawCount may await a later qualified slot.',
    'Matt_policy':'6 GiB owned-job cap; initial 5 GiB commit, 6 GiB physical and 4 GB disk; continuous 1 GiB commit, 3 GiB physical and 1 GB disk.',
    'read_only_system_snapshot':dict(snapshot(),disk_free_bytes=shutil.disk_usage(base).free),
    'outbound_action':False,
}
target=base/'root-three-source-importer-lease-20261005.json'
temporary=target.with_suffix('.json.tmp')
temporary.write_text(json.dumps(result,indent=2),encoding='utf8')
os.replace(temporary,target)
print(json.dumps({'status':result['status'],'receipt':target.name,'snapshot':result['read_only_system_snapshot']},indent=2))
