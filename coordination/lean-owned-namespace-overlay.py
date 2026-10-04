from pathlib import Path
import argparse,json,hashlib
p=argparse.ArgumentParser();p.add_argument('base',type=Path);p.add_argument('output',type=Path);p.add_argument('--extra',type=Path,action='append',default=[]);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);records=[]
for root in [a.base]+a.extra:
 for source in root.rglob('*'):
  if not source.is_file() or not (source.name.endswith(('.olean','.olean.private','.olean.server','.ir','.ilean'))):continue
  rel=source.relative_to(root);dest=a.output/rel;dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.exists() or dest.is_symlink():
   assert dest.is_symlink(),f'Refuse existing owned output {dest}'
   dest.unlink()
  dest.symlink_to(source.resolve());records.append({'path':str(rel),'origin':str(source.resolve()),'sha256':hashlib.sha256(source.read_bytes()).hexdigest()})
(a.output/'overlay-index.json').write_text(json.dumps(records,indent=2))
print('Single namespace file union ready; pinned artifact records',len(records))
