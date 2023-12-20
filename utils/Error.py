from colorama import Fore, Back, Style

ERROR_MESSAGE = f"{Style.BRIGHT + Fore.RED}[ERROR]{Style.RESET_ALL} ->   "

def ERROR(func):
    def wrapper(*args, **kwargs):
        print(f"{ERROR_MESSAGE}", end="")
        func(*args, **kwargs)
        exit()
    return wrapper


@ERROR
def FileNotFound(filepath: str) -> None:
    print(f"Parse Error - File {Fore.CYAN + filepath + Style.RESET_ALL} not Found.")


@ERROR
def inputFileFirstLineIncorrect(first: str, second: str, third: str) -> None:
    print(f"Parse Error - Header Line of input File incorrect: {Fore.CYAN +  first + ' ' + second + ' ' + third + Style.RESET_ALL}. Should be: {Fore.CYAN}p af <X>{Fore.RESET}, where <X> is a positive integer.")


@ERROR
def attackOnUnknownArgument(line_number: int, attack: str, defend: str):
    print(f"Parse Error - On Line {line_number}. Either {Fore.CYAN + attack + Style.RESET_ALL} or {Fore.CYAN + defend + Style.RESET_ALL} not registered.")


@ERROR
def firstLineParamAmountIncorrect():
    print(f"Parse Error - Header Line of input File does not fullfill requirements. Should be: {Fore.CYAN}p af <X>{Fore.RESET}, where <X> is a positive integer.")

@ERROR
def clusteringParseError(line_number: int):
    print(f"Parse Error - Cluster Definition incorrect at line {line_number}. Should be: {Fore.CYAN}<C> <- <X1> <X2> ...{Fore.RESET}, where <C> is the cluster name and <Xx> the arguments <C> is clustered.")

@ERROR
def clusteringArgumentDoesNotExist(line_number: int, argument: str):
    print(f"Parse Error - Argument {argument} does not exist at line {line_number}.")

@ERROR
def malformedLine(line_number: int, line: list):
    print(f"Parse Error - Malformed Line [{line_number}]: {Fore.CYAN}{' '.join(line)}{Fore.RESET}.")

@ERROR
def WrongInputFileending():
    print(f"Input File Error - Wrong Input File Ending. Should be: {Fore.CYAN}<X>.af{Fore.RESET}.")


@ERROR
def wrongAlgorithm(algo: str):
    print(f"Argument Error - Algorithm {Fore.CYAN}{algo}{Fore.RESET} is not valid. Chose between 'BFS' or 'DFS'")

@ERROR
def notEnoughArguments():
    print(f"Parse Error - More Arguments in Attacks then defined in p-Line.")


@ERROR
def wrongSemantic():
    print(f"Wrong semantic, valid semantics: {Fore.CYAN}CF{Fore.RESET}, {Fore.CYAN}AD{Fore.RESET}, {Fore.CYAN}ST{Fore.RESET}.")


@ERROR
def concretizeCLIARgumentInvalid(arg: str):
    print(f"Invalid argument {Fore.CYAN}{arg}{Fore.RESET} in program argument concretize list.")

@ERROR
def concretizeOfCluster(arg: str):
    print(f"Invalid argument {Fore.CYAN}{arg}{Fore.RESET}, can't concretize cluster.")