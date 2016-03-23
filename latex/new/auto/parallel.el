(TeX-add-style-hook
 "parallel"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("hyperref" "hidelinks") ("agda" "references" "links")))
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "graphicx"
    "hyperref"
    "agda"
    "amsmath"
    "amsthm"
    "mathtools"
    "textgreek"
    "catchfilebetweentags"
    "tipa"
    "bussproofs")
   (TeX-add-symbols
    '("swap" 3)
    '("var" 1)
    '("ap" 2)
    '("lambAg" 2)
    '("freshin" 2)
    '("choice" 2)
    "alp"
    "lam"
    "alpsy"
    "pr"
    "then"
    "inAg"
    "ninAg"
    "neqAg"
    "fv"
    "perm"
    "perma"
    "free"
    "choiceAg"
    "choiceAgaux"
    "alpeqAg")
   (LaTeX-add-labels
    "sec:parrallel")
   (LaTeX-add-environments
    "lem")))

