BEGIN {
    matched = 0
}
/^import.*/ {
    if (matched == 0) {
	print $0
	print "import qualified Data.Maybe"
	print "import qualified Data.List"
	print "import qualified Data.Char"
	print "import qualified Extraction"
	print "import qualified DiffStackT"
        matched = 1
        next
    }
}
{ print }
