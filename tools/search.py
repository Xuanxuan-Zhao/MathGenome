"""Search source knowledge IDs, mathematical topics or actual Lean declarations."""
from pathlib import Path
import argparse,json,re,sys,unicodedata
from zipfile import BadZipFile, ZipFile

def norm(text):
    return re.sub(r'[^\w]+',' ',unicodedata.normalize('NFKC',text).casefold()).strip()

def search(data,query,kind='entries'):
    tokens=norm(query).split(); rows=[]
    source=(data['entries']+data.get('supplemental_entries',[])) if kind=='entries' else [dict(name=n,**d) for n,d in data['declarations'].items()]
    for row in source:
        primary=' '.join(str(row.get(k,'')) for k in ('id','key','title','name','aliases'))
        text=norm(primary+' '+str(row.get('keywords',''))+' '+str(row.get('type',''))+' '+' '.join(row.get('declarations',[])))
        if all(t in text for t in tokens):
            score=sum(4 if t in norm(primary) else 1 for t in tokens)
            if norm(query)==norm(row.get('id',row.get('name',''))):score+=100
            rows.append((score,row))
    return [r for _,r in sorted(rows,key=lambda x:(-x[0],x[1].get('id',x[1].get('name',''))))]

def read_declarations(shards, read_shard):
    declarations = {}
    for shard in shards:
        part = json.loads(read_shard(shard))
        if declarations.keys() & part.keys():
            raise ValueError(f'Duplicate declarations in {shard}')
        declarations.update(part)
    return declarations


def read_index(path, kind):
    data = json.loads(path.read_text(encoding='utf-8'))
    if kind != 'declarations' or 'declarations' in data:
        return data
    shards = data['declaration_shards']
    if all((path.parent / shard).is_file() for shard in shards):
        data['declarations'] = read_declarations(shards, lambda shard: (path.parent / shard).read_bytes())
    else:
        tag = 'v' + data['release']
        archive = path.parent / f'mathgenome-{tag}-declarations.zip'
        if not archive.is_file():
            raise FileNotFoundError(f'Download {archive.name} from the {tag} GitHub Release '
                                    'and save it in catalog/.')
        with ZipFile(archive) as zipped:
            try:
                data['declarations'] = read_declarations(shards, zipped.read)
            except KeyError as error:
                raise ValueError(f'{archive.name} is missing a declaration shard: {error}') from error
    return data

def main():
    if hasattr(sys.stdout,'reconfigure'):sys.stdout.reconfigure(encoding='utf-8')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('query',nargs='+');p.add_argument('--kind',choices=['entries','declarations'],default='entries')
    p.add_argument('--limit',type=int,default=12);p.add_argument('--json',action='store_true')
    a = p.parse_args()
    try:
        data = read_index(Path(__file__).resolve().parents[1] / 'catalog/knowledge-index.json', a.kind)
    except (OSError, ValueError, BadZipFile) as error:
        p.error(str(error))
    rows=search(data,' '.join(a.query),a.kind)[:max(a.limit,0)]
    if a.json:print(json.dumps(rows,ensure_ascii=False,indent=2));return
    for r in rows:
        if a.kind=='entries':
            print(f"{r['id']}  {r['title']}\n  import {r['import']}")
            for n in r['preferred_mathlib_interfaces']:print('  preferred Mathlib: '+n)
            for n in r['declarations'][:6]:print('  '+n)
            if len(r['declarations'])>6:print(f"  ... {len(r['declarations'])} registered declarations (use --json)")
        else:print(f"{r['name']}\n  {r['file']}\n  {r['type']}\n  roles: {', '.join(r['curation_roles'])}")
    if not rows:print('No match. Try an English concept, source ID, or --kind declarations.')

if __name__=='__main__':main()
