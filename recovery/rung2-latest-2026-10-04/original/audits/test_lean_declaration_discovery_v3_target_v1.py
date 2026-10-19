#!/usr/bin/env python3
"""Pure scanner regression for the exact set-image token; no Lean jobs."""
from pathlib import Path
import ast,datetime,difflib,hashlib,json
HERE=Path(__file__).resolve().parent
BASE=HERE.parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(v):
 p=HERE/f'lean_declaration_discovery_v{v}.py';n={};exec(compile(p.read_bytes(),str(p),'exec'),n);return n
old,new=load(2),load(3)
assert sha(HERE/'lean_declaration_discovery_v2.py')=='7c6d90118ba03ea74d2bc4dbe5ddeb0938bb8485b68c4a03b827ae37776fdfeb'
assert sha(HERE/'audit_final_statements_v7.py')=='473c8adfebd3c2ff78325f8d6c10a66ded375fdf8a8f32ad6ab9e6aaef564fb1'
def selected(path,names,ns):
 tree=ast.parse(path.read_text());nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in names or isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id in names for t in n.targets)]
 exec(compile(ast.Module(body=nodes,type_ignores=[]),str(path),'exec'),ns)
ns={};selected(HERE/'test_lean_declaration_discovery_review_v1.py',{'wrap','cases'},ns)
baseline=ns['cases'];wrap=ns['wrap'];selected(HERE/'test_lean_declaration_discovery_v2.py',{'added'},ns)
baseline+=ns['added']
added=[
 ('image',wrap("def s := f '' A\ntheorem after_image : True := by trivial"),['s','after_image']),
 ('nested_image',wrap("def s := (f '' (g '' A))\ntheorem t : True := by trivial"),['s','t']),
 ('adjacent_set',wrap("def s := f ''A\ntheorem t : True := by trivial"),['s','t']),
 ('image_newline',wrap("def s := f ''\n  A\ntheorem t : True := by trivial"),['s','t']),
 ('primed_identifiers',wrap("def f''' := g''\ntheorem t'' : True := by trivial"),["f'''","t''"]),
 ('image_primed_identifiers',wrap("def f''' := g'' '' A'\ntheorem t'' : True := by trivial"),["f'''","t''"]),
 ('preimage',wrap("def s := f ⁻¹' A\ntheorem t : True := by trivial"),['s','t']),
 ('image_string',wrap('def s := "f \'\' A theorem hidden"\ntheorem t : True := by trivial'),['s','t']),
 ('image_raw_string',wrap('def s := r#"f \'\' A theorem hidden"#\ntheorem t : True := by trivial'),['s','t']),
 ('image_comment',wrap("/- f '' A theorem hidden /- g '' B -/ -/\ndef s := f '' A\n-- theorem fake\ntheorem t : True := by trivial"),['s','t']),
 ('image_character',wrap("def c : Char := '\\''\ndef s := f '' A\ntheorem t : True := by trivial"),['c','s','t']),
 ('malformed_triple',wrap("def s := f ''' A\ntheorem t : True := by trivial"),None),
 ('malformed_quad',wrap("def s := f '''' A\ntheorem t : True := by trivial"),None),
 ('apostrophe',wrap("def s := '\ntheorem t : True := by trivial"),None),
 ('axiom_after_image',wrap("def s := f '' A\naxiom hidden : False\ntheorem t : True := by trivial"),None),
 ('private_after_image',wrap("def s := f '' A\nprivate theorem hidden : True := by trivial"),None),
 ('macro_after_image',wrap('def s := f \'\' A\nmacro "hidden" : command => pure default'),None),
 ('notation_after_image',wrap('def s := f \'\' A\nnotation "hidden" => True'),None),
 ('quoted_after_image',wrap("def s := f '' A\ntheorem «hidden» : True := by trivial"),None),
 ('same_line_after_image',wrap("def s := f '' A; theorem t : True := by trivial"),None),
 ('outside_after_image',wrap("def s := f '' A")+"theorem outside : True := by trivial\n",None),
]
def run(helper,s):
 try:return {'namespace':(r:=helper['discover_declarations'](s))[0],'names':r[1]}
 except ValueError as e:return {'rejected':str(e)}
results=[]
for group,cases in [('baseline',baseline),('image_extension',added)]:
 for name,s,expected in cases:
  a=run(new,s);o=run(old,s)
  ok='rejected' in a if expected is None else a=={'namespace':'N','names':expected}
  if group=='baseline':ok=ok and a==o
  if 'rejected' not in a:
   masked=new['mask_lean_literals_and_comments'](s)
   ok=ok and len(masked)==len(s) and [i for i,c in enumerate(masked) if c=='\n']==[i for i,c in enumerate(s) if c=='\n']
  results.append({'group':group,'name':name,'old':o,'new':a,'pass':ok})
def astbody(s):
 t=ast.parse(s);t.body=t.body[1:];return ast.dump(t,include_attributes=False)
v7=(HERE/'audit_final_statements_v7.py').read_text();v8=(HERE/'audit_final_statements_v8.py').read_text()
assert astbody(v7)==astbody(v8.replace('lean_declaration_discovery_v3','lean_declaration_discovery_v2').replace('ExpandedStatements_v8','ExpandedStatements_v7'))
# All following text is still inspected: the image token itself is never blanked.
mask_checks=[]
for s in ["f '' O","f ⁻¹' O","f'''", "f ''(g '' O)"]:
 a=new['mask_lean_literals_and_comments'](s);mask_checks.append({'source':s,'pass':a==s})
for s in ["'\\''",'"f \'\' O"', 'r#"f \'\' O"#']:
 a=new['mask_lean_literals_and_comments'](s);mask_checks.append({'source':s,'pass':a==' '*len(s)})
target=BASE/'lean/PhysicalSpectatorL2BudgetTransport_v1.lean'
a=run(new,target.read_text());o=run(old,target.read_text())
expected=['physicalSpectatorReindexAt_symm_measurePreserving','physicalSpectatorReindexAt_regionL2Budget','physicalSpectatorReindexAt_locallyL2']
# Exact names manually checked against all three source declarations.
assert o == {'rejected':'unsupported apostrophe/character-literal syntax'}
assert a == {'namespace':'TheoremT.Continuum','names':expected}
receipts=[]
for p in (BASE/'logs/development').glob('PhysicalSpectatorL2BudgetTransport_v1-*.json'):
 d=json.loads(p.read_text())
 if d['exit_code']==0 and d['source_sha256']==sha(target):receipts.append({'path':str(p),'sha256':sha(p)})
assert receipts
notation=BASE.parents[1]/'formal/.lake/packages/mathlib/Mathlib/Data/Set/Operations.lean'
lines=[{'line':i,'text':s} for i,s in enumerate(notation.read_text().splitlines(),1) if 'infixr:80' in s and "''" in s]
assert len(lines)==1 and lines[0]['text']=='infixr:80 " \'\' " => image'
diff=''.join(difflib.unified_diff((HERE/'lean_declaration_discovery_v2.py').read_text().splitlines(keepends=True),(HERE/'lean_declaration_discovery_v3.py').read_text().splitlines(keepends=True),fromfile='helper_v2',tofile='helper_v3'))
diff+=''.join(difflib.unified_diff(v7.splitlines(keepends=True),v8.splitlines(keepends=True),fromfile='auditor_v7',tofile='auditor_v8'))
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S_%fZ')
p=HERE/f'AUDIT_FINAL_STATEMENTS_V8_DIFF_v1_{stamp}.patch';p.write_text(diff)
out={'scope':'Exact image token lexical recognition only; no Lean job or proof source edit','test_sha256':sha(Path(__file__)),'old_helper_sha256':sha(HERE/'lean_declaration_discovery_v2.py'),'new_helper_sha256':sha(HERE/'lean_declaration_discovery_v3.py'),'old_auditor_sha256':sha(HERE/'audit_final_statements_v7.py'),'new_auditor_sha256':sha(HERE/'audit_final_statements_v8.py'),'auditor_ast_invariant':True,'cases':results,'mask_checks':mask_checks,'actual_target':{'path':str(target),'sha256':sha(target),'old':o,'new':a,'manually_expected_exact_names':expected,'compile_receipts':receipts},'pinned_notation':{'path':str(notation),'sha256':sha(notation),'lines':lines},'diff':{'path':str(p),'sha256':sha(p)},'all_pass':all(x['pass'] for x in results+mask_checks)}
p=HERE/f'AUDIT_FINAL_STATEMENTS_V8_REGRESSION_v1_{stamp}.json';p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'receipt':str(p),'sha256':sha(p),'cases':len(results),'all_pass':out['all_pass'],'failures':[r for r in results+mask_checks if not r['pass']]}))
raise SystemExit(not out['all_pass'])
