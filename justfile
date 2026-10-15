run *args='':
    cabal run exes -- {{args}}

format:
    fourmolu -i compiler