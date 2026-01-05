# Install somac
echo "Installing somac..."
lake build somac

cp -f ./compiler/.lake/build/bin/somac ~/.sup/bin/somac

# Install haoma
echo "Installing haoma..."
cargo build --manifest-path ./haoma/Cargo.toml --release 

cp -f ./haoma/target/release/haoma ~/.sup/bin/haoma

# Install souls
echo "Installing souls..."
lake build souls

cp -f ./souls/.lake/build/bin/souls ~/.sup/bin/souls