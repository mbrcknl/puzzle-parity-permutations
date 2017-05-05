session Lib = HOL +
  theories [document=false]
    "lib/LaTeX_Rule_Sugar"
    "lib/Lib"

session Puzzle = Lib +
  options
    [ document_variants=Puzzle
    , document_output=document
    , document=pdf
    ]
  theories
    "Puzzle"
  theories [document=false]
    "extras/Parity_Swap"
    "extras/Puzzle_Bottom_Up"
    "extras/Parity_Inversions"
    "extras/Parity_Extras"
    "extras/Parity_Merge_Sort"
  document_files
    "root.tex"
    "permute-3.tex"

session Talk = Lib +
  options
    [ document_variants=Talk
    , document_output=document
    , document=pdf
    ]
  theories
    "ylj17/Talk"
  document_files
    "root.tex"
