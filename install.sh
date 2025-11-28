# Installs haoma (Rust) and souls (Haskell) to PATH

set -e

echo "Starting installation of soma ecosystem..."

# Install somac
echo "Installing somac..."
cabal install somac --overwrite-policy=always

# Install haoma
echo "Installing haoma..."
cargo install --path haoma

# Install souls
echo "Installing souls..."
cabal install souls --overwrite-policy=always

echo "Soma ecosystem installation complete!"