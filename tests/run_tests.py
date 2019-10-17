#!/usr/bin/python3

from utils import getAllTigerFiles, runTest
from error_list import error_list

class TestEtapa1():
    folders = ['good', 'syntax', 'type', 'wrong']

    def getRequeriments(self, file):
        REQUERIMENTS_KW = 'REQUERIMENTS'
        with open(file, 'r') as f:
            line = f.readline()
            if REQUERIMENTS_KW in line:
                idx = line.index(REQUERIMENTS_KW) + len(REQUERIMENTS_KW)
                if '*/' in line:                    
                    req = line[idx:line.index('*/')]
                else:
                    req = line[idx:]
                return filter(None, map(lambda x: x.strip(), req.split(' ')))
            return []

    def checkRequeriment(self, requeriment, output):
        if requeriment not in error_list:
            raise Exception(("El requerimiento '%s' no esta en la lista " + 
                "de errores. Agregar a error_list") % requeriment)
        for text_req in error_list[requeriment]:
            if text_req not in output:
                return False
        return True

    def printFails(self, fails):
        for fail in fails:
            fail_t = "FAIL", fail['file']
            print(fail_t)
            print('-' * len(fail_t))
            print("Expected:", fail['req'])
            print("Output:", fail['output'])
            print("")
    
    def runAll(self):
        fails = []
        files = getAllTigerFiles('.')
        for file in files:
            output = runTest(file)
            requeriments = self.getRequeriments(file)
            for requeriment in requeriments:                
                if not self.checkRequeriment(requeriment, output):
                    fails.append({ 
                        "file": file,
                        "output": output,
                        "req": requeriment
                    })
        self.printFails(fails)
    
if __name__ == "__main__":
    TestEtapa1().runAll()