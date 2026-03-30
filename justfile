bump-toolchain version:
    echo "leanprover/lean4:{{version}}" > lean-toolchain
    cd souls && echo "leanprover/lean4:{{version}}" > lean-toolchain && lake update
    cd compiler && echo "leanprover/lean4:{{version}}" > lean-toolchain && lake update
    lake update
