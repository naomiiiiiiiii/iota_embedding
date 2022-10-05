(TeX-add-style-hook
 "packages"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8")))
   (add-to-list 'LaTeX-verbatim-environments-local "minted")
   (TeX-run-style-hooks
    "inputenc"
    ""
    "upgreek"
    "geometry"
    "dsfont"
    "enumitem"
    "minted"
    "mathtools"
    "natbib"
    "graphicx"
    "amsmath"
    "amssymb"
    "fullpage"
    "etoolbox"
    "setspace"
    "pgffor")
   (TeX-add-symbols
    '("mor" 1)
    '("obj" 1)
    '("x" 1)
    '("case" 5)
    '("f" 2)
    '("spc" 1)
    "st"
    "dis"
    "conj"
    "imp"
    "range"
    "R"
    "N"
    "E"
    "Z"
    "e"
    "dd"
    "D"
    "p"
    "term"
    "size"
    "var"
    "subst"
    "aequiv"
    "bequiv"
    "val"
    "inj"
    "iso"
    "cross"
    "xor"
    "start"
    "ed"
    "mem"
    "preim"
    "im"
    "colim"))
 :latex)

