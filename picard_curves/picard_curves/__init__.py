from sage.all import magma

import os
import inspect
filename = inspect.getframeinfo(inspect.currentframe())[0];
__magmapath__ = os.path.dirname(filename) + "/magma/"
try:
    magma.AttachSpec(__magmapath__ + 'spec')
except RuntimeError as err:
    # the err comes with a endline
    print("RuntimeError exception caught, with error message:\n\t > %s\nWe weren't able to load the magma package and some functionality of the endomorphisms package will be limited." % str(err).rstrip('\n'))

from .picard_curves import *
from .tools import *
