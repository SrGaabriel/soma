run *args='':
    cabal run exes -- {{args}}

fmt:
    fourmolu -i compiler