from utils import Parser

class ArgumentationFramework:
        def __init__(self) -> None:
            self.arguments = dict()
            self.arg_amount = None

        def parseFile(self, filepath: str):
            parser = Parser.Parser()
            self.arguments, self.arg_amount = parser.parseFile(filepath)
