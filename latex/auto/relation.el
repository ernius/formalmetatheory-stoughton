(TeX-add-style-hook
 "relation"
 (lambda ()
   (TeX-run-style-hooks
    "latex2e"
    "../Relation"
    "article"
    "art10"
    "agda"
    "autofe"
    "amsmath"
    "amsthm"
    "thmtools"
    "amssymb"
    "amsfonts"
    "tikz"
    "subfig")
   (TeX-add-symbols
    '("transclos" 1)
    '("reducesn" 2)
    '("reduces" 2)
    "pred"
    "reduction")))

