# Install somac
echo "Installing somac..."
lake build somac

cp -f ./compiler-lean/.lake/build/bin/somac ~/.sup/bin/somac

# Install haoma
echo "Installing haoma..."
cargo install --path haoma

cp -f ./haoma/target/release/haoma ~/.sup/bin/haoma

# Install souls
echo "Installing souls..."
lake build souls

cp -f ./souls-lean/.lake/build/bin/souls ~/.sup/bin/souls