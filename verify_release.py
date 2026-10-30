#!/usr/bin/env python3
"""Authenticate exported source and inherited audit; this program does not run Lean."""
from pathlib import Path
import gzip, hashlib, json, re, sys, tomllib
ROOT=Path(__file__).resolve().parent
def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
    d=json.loads((ROOT/'verification/lean_source_manifest.json').read_text())
    mods={row['module'] for row in d['files'].values()}
    need(len(d['files'])==1751,'wrong Lean source count')
    external=set()
    for name,row in d['files'].items():
        raw=(ROOT/name).read_bytes()
        need(sha(raw)==row['sha256'],'source digest mismatch: '+name)
        need(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==row['git_blob'],'Git source mismatch: '+name)
        for line in raw.decode().splitlines():
            if line.startswith('import '):
                for m in line[7:].split():
                    if m.startswith('C13'):need(m in mods,'missing local import: '+m)
                    else:external.add(m.split('.')[0])
    need(external<={'Mathlib','Lean','Std','Init','Batteries','Aesop','Qq'},'unexpected external namespace: '+str(external))
    need((ROOT/'lean/lean-toolchain').read_text().strip()=='leanprover/lean4:v4.31.0-rc1','toolchain changed')
    cfg=tomllib.loads((ROOT/'lean/lakefile.toml').read_text())
    need(cfg['require'][0]['rev']=='0ed37c9258f123a2c76a2175596f75c2bd50f941','Mathlib pin changed')
    lock=json.loads((ROOT/'lean/lake-manifest.json').read_text())
    need(len(lock['packages'])==9 and all(p['type']=='git' and re.fullmatch('[0-9a-f]{40}',p['rev']) for p in lock['packages']),'dependency lock changed or private path dependency')
    log=gzip.decompress((ROOT/'verification/historical_axiom_audit.log.gz').read_bytes())
    need(sha(log)=='135372280b757e13aac432d8b6c3055fd1b44ff37e35ab01df5c4fcfdcbe6901','historical log changed')
    rows=[json.loads(line[5:]) for line in log.decode().splitlines() if line.startswith('DECL ')]
    need(len(rows)==76982,'historical declaration count')
    need(all(not x['unsafe'] and set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in rows),'historical axiom/unsafe audit failed')
    recorded={x['module']:x['source_sha256'] for x in json.loads((ROOT/'verification/historical_ROOT_FINAL_REPLAY_RECEIPT.json').read_text())['cached_dependencies'] if x['module'].startswith('C13')}
    need(recorded=={x['module']:x['sha256'] for x in d['files'].values()},'export differs from historical audited closure')
    result={'status':'PASS_SOURCE_EXPORT_AND_HISTORICAL_AUDIT_AUTHENTICATION','lean_modules':len(mods),'historical_audited_declarations':len(rows),'external_namespaces':sorted(external),'fresh_lean_build':'NOT_RUN_BY_THIS_SCRIPT','classification':'Explicit published mathematical premise; not Lean-proved'}
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
