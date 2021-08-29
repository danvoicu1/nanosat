Nanosat

	This explains only the "Run" of the program. For the "How", please read "PvsNP.pdf"

For the purpose of the document we will presume windows install

1. go to c:
1. git glone current verion
1. "extract here" NanoSat.zip
1. test installation
   1. cmd C:\nanosat\NanoSat\bin\Debug
   1. NanoSat.exe
      1. you should receive an error. it's fine:) 
         1. No formula input file was selected!
1. all tests are grouped by name
   1. Ex1: 
      1. extract 20.zip
      2. copy C:\nanosat\NanoSat\bin\Debug\NanoSat.exe to C:\nanosat\20
      3. run NanaoSat all
    2. Ex2:
       1. Extract UF125.538.100_size_125_all_sat.zip
       2. copy C:\nanosat\NanoSat\bin\Debug\NanoSat.exe to C:\nanosat\UF125.538.100_size_125_all_sat
       3. run NanaoSat all
1. all programs runs generate an excel result witch you can check.
   1. results_[FLAG]_run_[TIMESTAMP].csv
      1. *ex: results_all_run_of_28_8_2021_1_57_56.csv*
1. some directories are special - as I included other alghoritms for compare
	1. ex: **BigFormulae** - you can run in parallel
       1. *NanoSat.exe -all*
       1. *cryptominisat5-win-amd64-nogauss.exe* (https://github.com/msoos/cryptominisat/releases)          
       1. *rsat_2.01_win.exe* - (http://reasoning.cs.ucla.edu/rsat/download2.php)
          
