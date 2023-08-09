from colorama import Fore, Back, Style

ERROR = f"{Style.BRIGHT + Fore.RED}[ERROR]{Style.RESET_ALL} ->   "



def FileNotFound(filename: str, directory: str) -> None:
    print(f"{ERROR}File {Fore.CYAN + filename + Style.RESET_ALL} not Found. {Style.DIM}[{directory}]")
    exit()



def inputFileFirstLineIncorrect(first: str, second: str, third: str) -> None:
    print(f"{ERROR}Header Line of input File incorrect: {Fore.CYAN +  first + ' ' + second + ' ' + third + Style.RESET_ALL}. Should be: {Fore.CYAN}p af <X>{Fore.RESET}, where <X> is a positive integer.")
    exit()


