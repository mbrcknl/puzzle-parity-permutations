
COMMON_FILES= \
	document/root.tex \
	lib/LaTeX_Rule_Sugar.thy \
	lib/Lib.thy \
	ROOT

PUZZLE_FILES= \
	document/permute-3.tex \
	extras/Parity_Extras.thy \
	extras/Parity_Inversions.thy \
	extras/Parity_Merge_Sort.thy \
	extras/Parity_Swap.thy \
	extras/Puzzle_Bottom_Up.thy \
	Puzzle.thy

TALK_FILES= \
  ylj17/Talk.thy

all: Puzzle.pdf document/Talk.pdf

Puzzle.pdf: document/Puzzle.pdf
	cp document/Puzzle.pdf .

document/Puzzle.pdf: $(PUZZLE_FILES) $(COMMON_FILES)
	isabelle build -d . Puzzle

document/Talk.pdf: $(TALK_FILES) $(COMMON_FILES)
	isabelle build -d . Talk

