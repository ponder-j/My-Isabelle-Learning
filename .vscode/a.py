
import json

def update_snippet_keys(file_path):
    with open(file_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    new_data = {}
    for key, value in data.items():
        if 'body' in value and value['body']:
            # Construct the new key, e.g., "longlongleftarrow ⟽"
            new_key = f"{key} {value['body'][0]}"
            new_data[new_key] = value
        else:
            # If body is not present, keep the original key
            new_data[key] = value

    with open(file_path, 'w', encoding='utf-8') as f:
        json.dump(new_data, f, indent=2, ensure_ascii=False)

file_to_update = '/Users/ponder/Study/IsabelleCode/.vscode/isabelle.code-snippets'
update_snippet_keys(file_to_update)

print(f"Snippet keys in '{file_to_update}' have been updated.")

