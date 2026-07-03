import json

empty_kb = {"questions": []}

with open("knowledge_base.json", "w") as file:
    json.dump(empty_kb, file, indent=4)

print("PrimeRobo knowledge base has been completely reset!")