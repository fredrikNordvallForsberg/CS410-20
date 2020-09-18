# Installing Agda on Windows 10

This short guide will help you get Agda 2.6.1 running on a Windows 10 machine.

1\. Get the [Haskell Platform](https://www.haskell.org/platform/windows.html) and follow the instructions. You can use the minimal installer for this class. Note that you will need an administrave PowerShell prompt when installing Chocolatey.

2\. The current version of Haskell platform ships with GHC 8.10.2, which requires a small fix before installing Agda. 
Find the settings file for GHC, its usual location is `C:\ProgramData\chocolatey\lib\ghc\tools\ghc-8.10.2\lib\settings`. If this path is invalid, type `get-command ghc` in a new PowerShell prompt to find out your specific GHC installation directory.

Locate the line 
```
,("Merge objects command", "C:/GitLabRunner/builds/2WeHDSFP/0/ghc/ghc/inplace/mingw/bin/ld.exe")
```
and replace the path with the actual one for your environment using forward slashes (e.g. `"C:/ProgramData/chocolatey/lib/ghc/tools/ghc-8.10.2/mingw/bin/ld.exe"`).

3\. Run 
``` 
cabal update
cabal install alex happy Agda
```
This will compile Agda on your machine. The process might take very long time (> 30 minutes) and is quite memory intensive (make sure you have at least 4GB free). 

4\. Install emacs. You can get a Windows installer from [here](https://ftp.gnu.org/gnu/emacs/windows/emacs-27/).

5\. Create `%appdata%\.emacs.d\init.el` (also making `.emacs.d` if needed) and paste the following:
```
(load-file (let ((coding-system-for-read 'utf-8))
                (shell-command-to-string "agda-mode locate")))
```
(`%appdata%` usually expands to `C:\Users\<your username>\AppData\Roaming`).

6\. Get the [agda standard library](https://github.com/agda/agda-stdlib/archive/v1.3.zip). Unzip it to a destination of your choice, call that parent directory `$DIR`.

7\. Create `%appdata%\agda\libraries` and add the following line to it, replacing `$DIR` with the concrete path:
```
$DIR\agda-stdlib-1.3\standard-library.agda-lib
```

8\. Now you are ready to start working on your first coursework :slightly_smiling_face:. Good luck!
