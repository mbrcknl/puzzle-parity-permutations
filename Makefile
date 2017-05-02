
FILES= \
	document/root.tex \
	document/permute-3.tex \
	extras/Parity_Extras.thy \
	extras/Parity_Inversions.thy \
	extras/Parity_Merge_Sort.thy \
	extras/Parity_Swap.thy \
	extras/Puzzle_Bottom_Up.thy \
	lib/LaTeX_Rule_Sugar.thy \
	lib/Lib.thy \
	Puzzle.thy \
	ROOT

Puzzle.pdf: document/Puzzle.pdf
	cp document/Puzzle.pdf .

document/Puzzle.pdf: $(FILES)
	isabelle build -d . Puzzle

