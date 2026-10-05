from pathlib import Path
import gzip,json,hashlib,time
import numpy as np
import sys

root=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent/'luke-k4-ramsey'
target=root/'data/constructions/final3840.json.gz'
t=time.perf_counter();h=hashlib.sha256();byte_count=0
with gzip.open(target,'rb') as stream:
    while chunk:=stream.read(1024*1024):
        h.update(chunk);byte_count+=len(chunk)
assert h.hexdigest()=='05302cbc635e939cc41f4ba019cdcba80199b0b83563100bac0b1a0d9fff1a29'
with gzip.open(target,'rt',encoding='utf8') as stream:obj=json.load(stream)
Q=obj['edge_probability_denominator']; weights=obj['block_weights']
matrix=np.asarray(obj['red_probability_numerators'],dtype=np.int64)
N=len(weights)
assert N==3840 and Q==65536 and matrix.shape==(N,N)
assert all(w==1 for w in weights)
assert np.array_equal(matrix,matrix.T)
assert np.min(matrix)>=0 and np.max(matrix)<=Q
means=matrix.reshape(192,20,192,20).sum(axis=(1,3))
assert np.all(means%400==0)
coarse=means//400
base=json.loads((root/'data/constructions/base192.json').read_text(encoding='utf8'))
oldbase=np.asarray(base['red_probability_numerators'],dtype=np.int64)
assert oldbase.shape==(192,192)
expected=np.where(oldbase==35015,35139,oldbase)
assert np.array_equal(coarse,expected)
report={
 'repository':'https://github.com/lukevs/k4-ramsey',
 'source_revision':'2cf216ba885fbb1b2d1b2d4920efeaa6ba438842',
 'method':'Independent gzip SHA/CRC and ordinary NumPy shape, uniform weights, range, symmetry and every20x20blockmean check',
 'file':'data/constructions/final3840.json.gz',
 'compressed_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
 'uncompressed_sha256':h.hexdigest(),'uncompressed_bytes':byte_count,
 'N':N,'Q':Q,'square':True,'uniform_weights':True,'symmetric':True,'range_0_Q':True,
 'all_36864_coarse_block_means_match':True,
 'coarse_model_adjustment':'base192 explainer uses35015/65536; final witness coarse diagonal parameter is35139/65536',
 'minimum_numerator':int(matrix.min()),'maximum_numerator':int(matrix.max()),
 'seconds':round(time.perf_counter()-t,3),
 'limit':'This independently validates exact construction data and correspondence to the192-class coarse model. It is not an independent K4-density recount or proof of novelty. The Lean certificate replay and prior exact-value comparison are separate.'
}
out=Path(__file__).resolve().parent/'verification/luke-witness-data-check.json'
out.parent.mkdir(parents=True,exist_ok=True)
tmp=out.with_suffix('.json.tmp');tmp.write_text(json.dumps(report,indent=2),encoding='utf8');tmp.replace(out)
print(json.dumps(report,indent=2))
