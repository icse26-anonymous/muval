SCRIPT_DIR=$(cd $(dirname $0)/..; pwd)
timeout=10 options='-c ./config/solver/zunda_sat_vsids.json -p sat' $SCRIPT_DIR/run_bench.sh benchmarks/SAT/petite/*.cnf | LC_ALL=C sort