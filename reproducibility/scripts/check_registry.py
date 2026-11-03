from pathlib import Path
import json,sys
base=Path(__file__).resolve().parents[1]
rows=[json.loads(l.split('REGISTRY_JSON ',1)[1]) for l in Path(sys.argv[1]).read_text().splitlines() if 'REGISTRY_JSON ' in l]
names={r['name'] for r in rows};assert len(names)==len(rows)
for r in rows:
 assert set(r['axioms'])<={'propext','Classical.choice','Quot.sound'},r['name']
 assert r['module'] and r['source_line'] is not None,('MISSING_SOURCE_LOCATOR',r['name'])
statements=json.loads((base/'manifests/THEOREM-MAP.json').read_text())['rows'];defs=json.loads((base/'manifests/DEFINITION-MAP.json').read_text())['rows']
for r in statements+defs:
 assert set(r['declarations'])<=names,(r['number'],set(r['declarations'])-names)
assert len(statements)==65 and len(defs)==14
by_name={r['name']:r for r in rows}
for statement in statements:
 assert any(by_name[n]['is_theorem'] for n in statement['declarations']),('NO_ACTUAL_PROOF',statement['number'])
expected=json.loads((base/'evidence/ELABORATED-REGISTRY.json').read_text())['declarations']
assert {r['name']:r for r in expected}==by_name, 'APPROVED_ELABORATED_REGISTRY_OR_DEPENDENCY_CHANGE'
print(json.dumps({'approved_registry_all_fields_equal':True,'status':'PASS','theorem_occurrences':65,'mathematically_distinct_results':64,'definition_rows':14,'queried_declarations':len(rows),'definition_1_2_status':'Background prior-work definition: explicitly not encoded in pinned source; not represented as a checked theorem.'}))
