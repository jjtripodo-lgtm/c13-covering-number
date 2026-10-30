"""Regenerate/check the native literal header from the frozen proof inputs."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--proof-dir',type=Path,default=Path(__file__).resolve().parent.parent);p.add_argument('--check',action='store_true');a=p.parse_args()
expected={'minimum_link_catalog.json':'019af94696fb4cf543fbc741401141d53126200c3193a21193c6720f81a56510','known30_control.json':'d4e9e82febc3fdf7fa6c3832e1cebb8c71b75abda04e3879af216d264759ae4d'}
data={}
for name,digest in expected.items():
 raw=(a.proof_dir/name).read_bytes()
 if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('source byte integrity: '+name)
 data[name]=json.loads(raw)
c=data['minimum_link_catalog.json'];control=data['known30_control.json'];mask=lambda b:sum(1<<x for x in b)
s='#pragma once\n#include <array>\n#include <cstdint>\n'
s+='inline constexpr std::array<std::array<std::uint16_t,15>,68> CATALOG = {{\n'+',\n'.join('  {{'+','.join(str(mask(b)) for b in x['blocks'])+'}}' for x in c['classes'])+'\n}};\n'
s+='inline constexpr std::array<std::uint16_t,30> KNOWN30 = {{'+','.join(str(mask(b)) for b in control['blocks'])+'}};\n'
out=Path(__file__).with_name('catalog_bits.hpp')
if a.check:
 if out.read_bytes()!=s.encode():raise ValueError('generated native header drift')
else:out.write_text(s)
print(json.dumps({'status':'PASS_NATIVE_CATALOG_HEADER','source_sha256':expected,'header_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True))
