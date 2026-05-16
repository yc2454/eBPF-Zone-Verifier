#!/bin/bash
# Runs inside the VM. L3 sweep of /root/bcf/sweep collected programs.
S=/root/bcf/sweep
TL=/root/bcf/build/test_loader
PRODUCERS="shift_constraint stack_ptr_varoff system_monitor test_get_stack_rawtp trace_sys_enter_execve"
REJECTS="ksnoop tcp_conn_tuner unreachable_arsh xdp_synproxy_kern"

for p in $PRODUCERS; do
  dmesg -C
  out=$("$TL" "$S/$p.bpf.o" "$S/$p.bpf.o.bcf-bundle" 2>&1)
  rc=$?
  loaded=$(echo "$out" | grep -c "SUCCESS: loaded")
  errline=$(echo "$out" | grep -iE "bpf_object__load|libbpf:.*failed|ERROR|invalid|errno" | head -1)
  prev=$(dmesg | grep -c "bcf_bundle_prevalidate: all entries OK")
  ch=$(dmesg | grep -oE "bcf_canonical_hash: buf.len=[0-9]+ hash=0x[0-9a-f]+" | tr '\n' ' ')
  einval=$(echo "$out" | grep -c "Invalid argument")
  if [ "$loaded" -ge 1 ]; then verdict="LOADED(stage6-discharged)"; else verdict="FAIL rc=$rc ${errline}"; fi
  echo "PRODUCER $p :: $verdict :: prevalidate_ok=$prev :: kernel_hash=[$ch]"
done

for p in $REJECTS; do
  dmesg -C
  out=$("$TL" "$S/$p.bpf.o" 2>&1)
  rc=$?
  loaded=$(echo "$out" | grep -c "SUCCESS: loaded")
  errline=$(echo "$out" | grep -iE "bpf_object__load|libbpf:.*failed|ERROR|invalid|errno|EACCES|EINVAL" | head -1)
  if [ "$loaded" -ge 1 ]; then verdict="LOADED(*** FALSE-ACCEPT vs zovia-reject ***)"; else verdict="kernel-REJECT(correct) ${errline}"; fi
  echo "REJECT   $p :: $verdict"
done
