#!/usr/bin/env python3
"""Offline, stdlib-only referee replay. Native C++ is an optional extra."""
import argparse,concurrent.futures,hashlib,json,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PROOF=ROOT/'source/research/horizonmath/c13_classified_pencils'

def need(ok,msg):
    if not ok:raise RuntimeError(msg)

def integrity():
    rows=json.loads((ROOT/'MANIFEST.json').read_text())['files']
    for name,expected in rows.items():
        p=ROOT/name
        need(p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==expected,'File integrity: '+name)
    return len(rows)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check-only',action='store_true');ap.add_argument('--native',action='store_true');args=ap.parse_args()
    count=integrity();out=ROOT/'replay-output';out.mkdir(exist_ok=True)
    jobs=[('tests-normal',[sys.executable,'-m','unittest','test_classified_pencils','test_classification_dependency_lock','-v'],PROOF,False),('tests-optimized',[sys.executable,'-O','-m','unittest','test_classified_pencils','test_classification_dependency_lock','-v'],PROOF,False),('adversarial',[sys.executable,str(ROOT/'adversarial_audit.py')],ROOT,True),('adversarial-O',[sys.executable,'-O',str(ROOT/'adversarial_audit.py')],ROOT,True)]
    if not args.check_only:
        for name,script in [('primary','verify_pencils.py'),('independent','independent_raw_replay.py')]:
            for optimized in (False,True):jobs.append((name+('-O' if optimized else ''),[sys.executable]+(['-O'] if optimized else [])+[script],PROOF,True))
    def execute(job):
        name,cmd,cwd,parse=job;start=time.monotonic()
        p=subprocess.run(cmd,cwd=cwd,capture_output=True,text=True)
        (out/(name+'.log')).write_text(p.stdout+p.stderr)
        need(p.returncode==0,name+' failed; inspect replay-output')
        if parse:(out/(name+'.json')).write_text(p.stdout)
        return name,{'exit_code':p.returncode,'seconds':round(time.monotonic()-start,3)}
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:results=dict(pool.map(execute,jobs))
    def read(name):return json.loads((out/(name+'.json')).read_text())
    need(read('adversarial')==read('adversarial-O'),'adversarial normal/-O difference')
    if not args.check_only:
        for name,stored in [('primary','primary_replay.json'),('independent','independent_replay.json')]:
            need(read(name)==read(name+'-O'),'normal/-O difference: '+name)
            need(read(name)==json.loads((PROOF/stored).read_text()),'frozen replay difference: '+name)
        sys.path.insert(0,str(PROOF));import release_gate
        release_gate.check_manifest();release_gate.check_headline(read('primary'),read('independent'))
        if args.native:results['native']=release_gate.run_native()
    elif args.native:raise RuntimeError('--native requires the full replay')
    receipt={'status':'PASS_PORTABLE_CONTROLS' if args.check_only else 'PASS_PORTABLE_C13_REPLAY','manifest_files':count,'runs':results,'native_requested':args.native,'published_classification':'External theorem input; not proved by this driver','lean_rebuild':'NOT_RUN; not needed by computational proof','external_referee_review':'NOT_PERFORMED'}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print(json.dumps(receipt,indent=2,sort_keys=True))

if __name__=='__main__':main()
