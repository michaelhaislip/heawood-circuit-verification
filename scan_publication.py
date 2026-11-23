"""Heuristic prepublication scan. Never prints matched secret contents."""
import argparse, json, pathlib, re, zipfile

PATTERNS = {
    'private key': r'-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----',
    'GitHub token': r'\b(?:gh[pousr]_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{30,})\b',
    'cloud access key': r'\b(?:AKIA|ASIA)[A-Z0-9]{16}\b',
    'API token': r'\bsk-[A-Za-z0-9_-]{24,}\b',
    'credential assignment': r'''(?i)(?:password|api_key|access_token|client_secret)\s*[:=]\s*["'][^"'\s]{8,}["']''',
    'Windows absolute path': r'(?i)\b[A-Z]:[\\/]',
    'home directory': r'/(?:Users|home)/[^\s/<>]+/',
    'email address': r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b',
    'lease UUID': r'\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b',
}
def main():
    p=argparse.ArgumentParser()
    p.add_argument('target', nargs='?', default='.')
    a=p.parse_args(); target=pathlib.Path(a.target)
    if target.is_file() and zipfile.is_zipfile(target):
        with zipfile.ZipFile(target) as z:
            items=[(n,z.read(n)) for n in z.namelist() if not n.endswith('/')]
    else:
        items=[(v.relative_to(target).as_posix(),v.read_bytes()) for v in target.rglob('*')
               if v.is_file() and not any(s in v.relative_to(target).parts for s in ('.git','__pycache__','.venv'))]
    findings=[]
    for name,b in items:
        if name.endswith('scan_publication.py'):
            continue  # Pattern definitions deliberately contain example signatures.
        try: t=b.decode('utf-8-sig')
        except UnicodeDecodeError:
            findings.append({'file':name,'category':'non-text file requiring review'}); continue
        for category,pattern in PATTERNS.items():
            if re.search(pattern,t): findings.append({'file':name,'category':category})
    print(json.dumps({'files_examined':len(items),'findings':findings,
                      'status':'PASS' if not findings else 'REVIEW'},indent=2))
    raise SystemExit(bool(findings))
if __name__=='__main__': main()
