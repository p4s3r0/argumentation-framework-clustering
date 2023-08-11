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
