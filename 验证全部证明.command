#!/bin/zsh
# Finder opens .command files in Terminal; the same check is available in VS Code.
cd -- "${0:A:h}" || exit 1
export PATH="$HOME/.elan/bin:$PATH"
unset LEAN_PATH LEAN_SRC_PATH

finish() {
  local result=$1
  print
  read 'reply?按回车关闭此窗口。'
  exit "$result"
}

if ! command -v lake >/dev/null || ! command -v python3 >/dev/null; then
  print -r -- '请先按照 README.md 安装 Lean（elan）和 Python 3.9 或更新版本。'
  finish 1
fi

print -r -- '准备项目固定版本的依赖；首次运行需要联网下载。'
lake exe cache get || finish $?
mkdir -p verification || finish $?
print -r -- '开始完整验证：每个 Lean 文件都会重新编译并检查公理依赖。'
print -r -- '进度显示在此窗口，报告保存到 verification/verification.json。'
python3 -u verify.py 2>&1 | tee verification/manual-build.log
verification_status=${pipestatus[1]}
if (( verification_status == 0 )); then
  print -r -- '完整验证成功。详细计数见上方输出和验证报告。'
else
  print -r -- '验证未完成或发生错误，请查看上方输出；这不代表验证通过。'
fi
finish "$verification_status"
