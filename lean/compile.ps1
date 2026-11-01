param([Parameter(ValueFromRemainingArguments = $true)][string[]]$LakeArguments)

# 全工作区共用两个编译名额，避免多个代理同时载入大型库耗尽内存。
$compileGate = [System.Threading.Semaphore]::new(2, 2, 'Local\CopyQuantumMetrologyLeanCompile')
$compileAcquired = $false
try {
    $compileAcquired = $compileGate.WaitOne()
    $env:LEAN_NUM_THREADS = '2'
    & lake @LakeArguments
    $compileExit = $LASTEXITCODE
} finally {
    if ($compileAcquired) { [void]$compileGate.Release() }
    $compileGate.Dispose()
}
exit $compileExit
