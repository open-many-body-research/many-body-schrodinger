from pathlib import Path
import hashlib,json,sys,datetime
B=Path(__file__).resolve().parents[1]; A=B/'audits'; L=B/'lean'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def rec(p): return {'path':str(p.relative_to(B)),'sha256':sha(p),'bytes':p.stat().st_size}
r=A/'formal_semantics/20260910T203703_121453Z/receipt.json'; review=Path(sys.argv[1]).resolve(); d=json.loads(r.read_text())
assert d['exit_code']==0 and not d['unexpected_axioms'] and d['axiom_report_complete'] and d['printer_ellipsis_count']==0
assert len(d['expected_declarations'])==28 and 'TheoremT.Continuum.pairCenterEquiv_apply' in d['expected_declarations']
for x in d['module_records']:
 assert not x['forbidden_source_tokens'] and x['source_unchanged_during_audit'] and x['object_unchanged_during_audit']
 for k in ('source','object'): assert sha(Path(x[k]))==x[k+'_sha256']
mods=['KSScaledPrincipal_v1','KSScaledPrincipalIBP_v1','KSScaledLocalWeakKernel_v1','PairKSLift_v1','PairCoordinatesLaplacian_v1','PairKSPrincipalIdentity_v1','PairKSPotential_v1','PairKSPotentialSmooth_v1','CoulombPairKSClassical_v1','CoulombPairKSWeak_v1','CoulombSpinPairKSWeak_v1']
rows=[]
for m in mods:
 s=L/(m+'.lean'); o=L/'build'/(m+'.olean'); choices=[]
 for dev in (B/'logs/development').glob(m+'-*.json'):
  v=json.loads(dev.read_text())
  if v['exit_code']==0 and v['source_sha256']==sha(s): choices.append(dev)
 assert choices,m
 rows.append({'module':m,'source':rec(s),'object':rec(o),'development_receipt':rec(sorted(choices)[-1])})
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FORMAL_ACTUAL_N2_PAIR_KS_WEAK_EQUATION','sources':rows,'strict_parent_receipt':rec(r),'parent_declarations':28,'child_support_checkpoints':[rec(A/'KS_SCALED_PRINCIPAL_CHECKPOINT_v1.json'),rec(A/'PAIR_KS_POTENTIAL_CHECKPOINT_v1.json')],'total_new_modules':11,'total_audited_declarations':41,'final_receipt_binding_review':rec(review),'independent_review_status':'Substantive child source review completed before interruption; final receipt review will be linked by a separate immutable record.','manuscript':rec(B/'paper/COULOMB_PAIR_KS_WEAK_FORMAL_v1.md'),'auditor':rec(A/'audit_final_statements_v5.py'),'declaration_discovery':rec(A/'lean_declaration_discovery_v1.py'),'auditor_root_review':rec(A/'AUDIT_FINAL_STATEMENTS_V5_ROOT_REVIEW_v1.json'),'seal_script':rec(Path(__file__).resolve()),'exact_scope':{'inputs':'N=2 actual scalar or full fermionic-spin weak H2 Coulomb eigen-equation, all real Z,E.','map':'x0=t+KS(y)/2, x1=t-KS(y)/2; actual unscaled center coordinates.','principal':'c=1; Delta_y+|y|^2 Delta_t is 2|y|^2 times physical Laplacian.','coefficient':'4+4|y|^2(-Z/|x0|-Z/|x1|-E), smooth on the open patch excluding nuclear zeros, equal to 4 on pair fiber.','conclusion':'Actual integrability and zero compact-test splitGrushin integral across y=0; common full-spin representative, ae/permutation/square-sum properties preserved.','not_assumed':'No derivatives at fiber, off-zero weak equation, analyticity, binding, uniqueness or gap beyond actual eigen-equation.'},'cache_disclosure':'Pinned existing development dependency objects reused; no isolated source rebuild in this unit.','unused_auditor_draft':{**rec(A/'audit_pair_ks_statements_v1.py'),'status':'unexecuted and superseded by root-reviewed shared v5'},'limitations':['No triple nuclear/pair intersection.','No uniform factorial estimates or global dictionary theorem.','No isolated source rebuild or full Theorem T.'],'next':'Actual epsilon-scaled nuclear/pair weak equations and originScaledDifference forcing; preserve epsilon electron repulsion. Root owns direct scalar/spin pair local H2 composition.','frozen_provenance':{'commit':'166f43f2f0178f92d8c4d1dde209ef0eeaefa660','tag':'theorem-t-proof-freeze-2026-09-09','path':'rwa_proof/UNIFORM_ANALYTIC_AUDIT.md','sha256':'5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c'}}
p=A/'COULOMB_PAIR_KS_WEAK_CHECKPOINT_v1.json'
with p.open('x') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(rec(p)))
