"""Compare actual full elaborated type ASTs/dependency sets with the approved baseline."""
from pathlib import Path
import json,sys
base=Path(__file__).resolve().parents[1]
actual=[json.loads(line.split('CONTENT_JSON ',1)[1]) for line in Path(sys.argv[1]).read_text().splitlines() if 'CONTENT_JSON ' in line]
expected=json.loads((base/'manifests/ELABORATED-CONTENT-BASELINE.json').read_text())['declarations']
by=lambda rows:{r['name']:r for r in rows}
assert len(actual)==len(expected)==5298 and len(by(actual))==5298
assert by(actual)==by(expected), 'ELABORATED_TYPE_OR_DEPENDENCY_CHANGE'
print(json.dumps({'status':'PASS','declarations':5298,'full_elaborated_type_asts_equal':True,'type_and_value_dependency_sets_equal':True,'source_metadata_ignored':True,'scope':'Every own-library declaration, including generated/private constants. This does not compare docstrings or raw .olean bytes.'}))
