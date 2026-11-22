#!/bin/bash
# Compares the software instruction counters a Colab VM can run (row
# BENCH-vm-no-instruction-counter): the DynamoRIO client zed_icount, DynamoRIO's sample client
# inscount, valgrind's callgrind, and QEMU user mode with its plugin libinsn.so where the
# installed QEMU has it. For each it prints the count of `selftest work <n>` at two sizes, twice,
# and the seconds each run took, next to the native run. Installs what is missing (as root, on a
# VM). Usage: tools/icount/compare.sh <n> <out dir>; run from the checkout's root.
# The results of 2026-11-22 are in the comment at zed_tests::scaling::Meter::new.
n=${1-}
out=${2-}
[[ $n =~ ^[0-9]+$ ]] && [[ $out == /?* ]] || { echo "usage: $0 <n> <out dir>" >&2; exit 2; }
big=$((8 * n))
dr=/opt/dynamorio
bash tools/icount/install-dynamorio.sh "$dr" || exit 1
apt-get install -y -qq valgrind qemu-user > "$out/apt.log" 2>&1
client=$(bash tools/icount/build.sh "$dr" "$out/icount") || exit 1
self=$out/icount/zed_icount_selftest
echo "selftest under the client:"; cat "$out/icount/selftest.log"
echo "selftest natively (3 = no software counter):"; "$self"; echo "exit $?"
echo "does DynamoRIO follow execve (0 = selftest ran under the client):"
"$dr/bin64/drrun" -c "$client" -- /bin/sh -c "$self > /dev/null"; echo "exit $?"
echo "/proc/self/exe under DynamoRIO:"; "$dr/bin64/drrun" -- /bin/readlink /proc/self/exe
qplugin=$(find / -xdev -name 'libinsn.so' -path '*qemu*' 2>/dev/null | head -1)
echo "qemu: $(qemu-x86_64 --version | head -1); libinsn.so: ${qplugin:-none}"
t() { /usr/bin/time -f "%e" -o "$out/t" "$@" > "$out/o" 2>&1; echo "$(tail -c 300 "$out/o" | tr '\n' ' ') secs=$(cat "$out/t")"; }
for size in $n $big; do
  for run in 1 2; do
    echo "size $size run $run"
    echo "  native:    $(t "$self" work $size)"
    echo "  zed_icount: $(t "$dr/bin64/drrun" -c "$client" -- "$self" work $size)"
    echo "  inscount:  $(t "$dr/bin64/drrun" -c "$dr/samples/bin64/libinscount.so" -- "$self" work $size)"
    echo "  callgrind: $(t valgrind --tool=callgrind --callgrind-out-file=$out/cg.out "$self" work $size) $(command grep -a '^summary' $out/cg.out)"
    if [ -n "$qplugin" ]; then
      echo "  qemu:      $(t qemu-x86_64 -plugin "$qplugin" -d plugin "$self" work $size)"
    fi
  done
done
cp "$self" "$out/selftest-binary"
