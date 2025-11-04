# Default folders if none are provided
if (($# == 0)); then
    set -- tests/simple tests/medium tests/hard
fi

total_passed=0
total_failed=0

test_one_file() {
    local file="$1"
    local minisat_out cargo_out

    minisat_out=$(minisat "$file" 2>&1 | awk 'NF{last=$NF} END{print last}')
    cargo_out=$(cargo run --quiet <"$file" 2>&1 | awk 'NF{last=$NF} END{print last}')

    if [[ "$minisat_out" == "$cargo_out" ]]; then
        echo -e "\e[32mPassed\e[0m $file"
        return 0
    else
        echo -e "\e[31mFailed\e[0m $file"
        echo "  minisat: $minisat_out | yours: $cargo_out"
        return 1
    fi
}

for dir in "$@"; do
    [[ -d "$dir" ]] || {
        echo "Skipping missing dir: $dir"
        continue
    }

    echo "=== Running in: $dir ==="
    passed=0
    failed=0

    # Find CNF files recursively
    while IFS= read -r -d '' file; do
        if test_one_file "$file"; then
            ((passed++))
        else
            ((failed++))
        fi
    done < <(find "$dir" -type f -name '*.cnf' -print0 | sort -z)

    echo "Folder summary ($dir): Passed=$passed Failed=$failed"
    ((total_passed += passed))
    ((total_failed += failed))
done

echo "========================"
echo "Total Passed: $total_passed"
echo "Total Failed: $total_failed"
