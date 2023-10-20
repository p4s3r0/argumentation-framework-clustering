from . import ConflictFreeSolver
from . import AdmissibleSolver
from . import StableSolver

from utils import Error
from utils import Argument


def getSemanticSolver(semantic: str, AF: dict[str, Argument.Argument]):
    if semantic == "CF":
        return ConflictFreeSolver.ConflictFreeSolver(AF=AF)
    elif semantic == "AD":
        return AdmissibleSolver.AdmissibleSolver(AF=AF)
    elif semantic == "ST":
        return StableSolver.StableSolver(AF=AF)
    else:
        Error.wrongSemantic()

    

            