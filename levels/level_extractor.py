import re

with open('microban.txt', 'r') as file:
    contents = file.read()

puzzles = re.split(r'^\s*;\s*.*\s*\n', contents, flags=re.MULTILINE)
del puzzles[0]
# puzzles = [puzzle.strip() for puzzle in puzzles if puzzle.strip()]

for i, puzzle in enumerate(puzzles):
    with open(f"{i+1}.txt", "w") as output_file:
        output_file.write(puzzle)
