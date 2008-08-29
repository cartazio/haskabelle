
# This script invokes "ghc -cpp -E" on all literate Haskell files causing
# the translation into ordinary Haskell source files, where all pragmas
# are resolved. The resulting ".hspp" files are renamed to ".hs" files.
#
# "ghc -cpp -E" basically runs the literate pre-processor and afterwards
# the C pre-processo

import os

srcdir = "/home/paba/studies/NICTA/hsimp/ref/refine/haskell/src/"

for (dir, dirs, files) in os.walk(srcdir) :
    for file in files :
        if file.endswith(".lhs") or file.endswith(".lhs-boot"):
            fp = os.path.join(dir,file)
            print os.system("ghc -cpp -E " + fp)

for (dir, dirs, files) in os.walk(srcdir) :
    for file in files :
        if file.endswith(".hspp"):
            fp = os.path.join(dir,file)
            fp2 = os.path.join(dir,file[0:-2])
            os.rename(fp, fp2)
