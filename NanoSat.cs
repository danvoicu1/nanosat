using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text;

namespace NanoSat
{
    //August 2021
    // Copyright (c) 2021 Dan Voicu

    //Permission is hereby granted, free of charge, to any person obtaining a copy
    //of this software and associated documentation files (the "Software"), to deal
    //in the Software without restriction, including without limitation the rights
    //to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
    //copies of the Software, and to permit persons to whom the Software is
    //furnished to do so, subject to the following conditions:

    //The above copyright notice and this permission notice shall be included in all
    //copies or substantial portions of the Software.

    //THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    //IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    //FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    //AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    //LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    //OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
    //SOFTWARE.

    //NOTES:
    // - the current implementation of NanoSat only accepts 3-members clauses formulae
    // - it does not check for duplicate clauses
    // - it does not check for tautology whithin clauses
    // - it does not check for missing literals whithin formulae
    // - it does not check for pure literals
    // - the calculations of a run complexity is only an approximation
    // - the pretty-printing may bail the execution out, if the cmd window is not sized wide enough (unless someone fixes this...)
    // - negative polarity literals' index are represented as index + n (ex: for n = 100, -X11 is represented as X111)
    internal class NanoSat
    {
        #region engine globals

        private static int n;//number of inputs
        private static int m; //number of clauses
        private static int[] a; //column "a" from the input file
        private static int[] b; //column "b" from the input file
        private static int[] c; //column "c" from the input file
        private static bool[] header; //history of used literals as headers
        private static Hashtable history; //history of the reached states, in the NanoSat algorithm description document is referred to as MDB (Memory Data Base)
        private static List<int>[] adj_opp; //adjancences of all opposite literals
        private static int starting_Xk = 0; //literal's index, the algorithm starts with - this can be any from 1 to n & -1 to -n
        private static List<int> lambda; //the list that will contain n literals at the end of the run if the formulae has at least one SAT solution

        #endregion engine globals

        #region switches

        /// <summary>
        /// Execution switches
        /// </summary>
        ///

        private static bool runAll = false;
        private static bool exhaustive = false;
        private static bool stopOnFailure = false;
        private static bool displaySolution = false;
        private static bool statsRecordRun = false;

        #endregion switches

        #region stats

        /// <summary>
        /// The following variables are used for statistics purposes only
        /// </summary>
        ///

        private static List<long> stats_lambda_size_history = new List<long>();
        private static List<long> stats_lambda_Xk_history = new List<long>();
        private static List<long> stats_lambda_Xj_history = new List<long>();
        private static ulong stats_main_loop_cnt = 0uL;
        private static int stats_base_literal = 0;
        private static ulong stats_get_opp_units_cnt = 0uL;
        private static ulong stats_get_units_cnt = 0uL;
        private static ulong stats_find_units_cnt = 0uL;
        private static string currentFormula = "";
        private static double complexity_order = 0.0;
        private static string results = "";
        private static string results_dir = "";
        private static double complexity_counter = 0.0;

        #endregion stats

        private static void Main(string[] args)
        {
            if (args.Length != 0)
            {
                if (args[0].ToUpper().Contains("ALL"))
                    runAll = true;
                else
                    currentFormula = args[0];
                //setup the execution flags
                if (args.Length > 1)
                    for (int i = 1; i < args.Length; i++)
                        if (args[i].ToUpper().Contains("EXH"))
                            exhaustive = true;
                        else if (args[i].ToUpper().Contains("STP"))
                            stopOnFailure = true;
                        else if (args[i].ToUpper().Contains("REC"))
                            statsRecordRun = true;
                        else if (args[i].ToUpper().Contains("SOL"))
                            displaySolution = true;

                RunFormulae();
            }
            else
            {
                ConsoleColor clr = Console.ForegroundColor;
                Console.ForegroundColor = ConsoleColor.Red;
                Console.WriteLine("No formula input file was selected!\n\rPlease select a .cnf file in DIMACS format and rerun!");
                Console.ForegroundColor = clr;
            }
        }

        #region engine

        /// <summary>
        /// Main 3-SAT engine
        /// Receives the initial literal the process will start with
        /// If a solution is found it returns "true", while lambda will contain n literals as solution
        /// The indexes of positive literals are as such, while their opposite are used as index + n
        /// Execution complexity: O(n^2)
        /// </summary>
        /// <param name="input"></param>
        /// <returns></returns>
        private static bool RunEngine(int input)
        {
            bool isSat = true;
            InitStats();
            header = new bool[2 * n + 1];
            starting_Xk = input;
            int Xk = starting_Xk;
            stats_base_literal = starting_Xk;
            header[Xk] = true;
            lambda.Add(Xk);
            bool flip = false;
            Stopwatch stopwatch = new Stopwatch();

            stopwatch.Start();
            while ((lambda.Count != 0 || IncrementHeader(ref Xk)) && lambda.Count < n)
            {
                //selecting the next Xk: whatever comes next
                //this replaces the need of using the non_lambda structure
                while (lambda.Contains(Xk) || lambda.Contains(Opposite(Xk))) Xk = Xk % (2 * n) + 1;
                lambda.Add(Xk);

                //calling the main execution block
                isSat = SaveState() && GetAllUnits();

                //if the state was already visited or a collision was detected
                if (!isSat || (lambda.Count == n && !CheckBinarySolution()))
                {
                    flip = !flip;
                    lambda.Remove(Xk);
                    Xk = Opposite(Xk);
                    if (!flip)
                    {
                        //the try the opposite(Xk)
                        lambda.Remove(lambda.Last());
                        //At this point both Xk polarities have been tested
                        if (lambda.Count == 1)
                        {
                            //if Xk is the only element in the list
                            //then there is no point in using it or its opposite polarity
                            //as lambda's header
                            header[Xk] = true;
                            header[Opposite(Xk)] = true;
                        }
                    }
                }
                else
                {
                    //attempting to save the new lambda state in case new units were added
                    //then reset the flipping flag
                    SaveState();
                    flip = false;
                }
                //statistics
                UpdateStats(Xk);
            }
            stopwatch.Stop();

            return ValidateSolution(stopwatch);
        }

        /// <summary>
        /// Saves the current state of lambda in the history hash table.
        /// If that state is not already contained in it - then returns "true"
        /// If the current state already exists, it doesn't add a duplicate and returns "false"
        /// Execution complexity: O(n)
        /// </summary>
        /// <returns></returns>
        private static bool SaveState()
        {
            List<int> tmp = lambda.ToList();
            tmp.Sort();
            string source = "";
            foreach (int item in tmp) source = source + item + ",";
            byte[] b = MD5.Create().ComputeHash(Encoding.UTF8.GetBytes(source));
            source = Encoding.UTF8.GetString(b);

            bool isSat = !history.ContainsKey(source);
            //if this is a newlly visited state then add it to the history structure
            if (isSat)
                history.Add(source, lambda.Count);

            IncrementComplexity(lambda.Count);

            return isSat;
        }

        /// <summary>
        /// Loops through the entire lambda collection searching for units resulted from pairs of values from lambda
        /// as well as from each individual member of lambda based on its opposite polarity
        /// In case a collision is detected it returns "false" while lambda is being restored to its original/entry values
        /// otherwise lambda will contain the newlly-found units if any and the method returns "true"
        /// Excution complexity: O(lambda.Count) * O(GetUnits) + O(lambda.Count) * O(GetOppUnits)) = O (n^2)
        /// </summary>
        /// <returns></returns>
        private static bool GetAllUnits()
        {
            bool isSat = true;

            List<int> tmp = lambda.ToList();
            List<int> orig = lambda.ToList();
            int k = 0;
            for (k = 0; k < tmp.Count && isSat; k++)
                isSat = GetUnits(lambda[k]);

            if (isSat)
            {
                IncrementComplexity(lambda.Count);
                tmp = lambda.ToList();

                for (k = 0; k < tmp.Count && isSat; k++)
                    isSat = GetOppUnits(lambda[k]);
            }

            //if a collision was detected then restore lambda
            if (!isSat)
                lambda = orig.ToList();

            return isSat;
        }

        /// <summary>
        /// Searching for anits based on the opposite of one literal (Xk)
        /// In case a collision is detected it returns "false" while lambda remains untouched
        /// Otherwise lambda will also contain the newlly found units, if any
        /// Execution complexity:  O(sigma(Opposite(Xk))) * 2 * O(GetUnits)) = O(n)
        /// </summary>
        /// <param name="Xk"></param>
        /// <returns></returns>
        private static bool GetOppUnits(int Xk)
        {
            stats_get_opp_units_cnt++;
            bool isSat = true;
            for (int i = 0; i < adj_opp[Xk].Count && isSat; i += 2)
            {
                int val_b = adj_opp[Xk][i];
                int val_c = adj_opp[Xk][i + 1];
                isSat = !(lambda.Contains(Opposite(val_b)) && lambda.Contains(Opposite(val_c))) &&
                    ((lambda.Contains(val_b) || lambda.Contains(val_c) || GetUnits(val_b) || GetUnits(val_c)));
            }
            IncrementComplexity(adj_opp[Xk].Count);
            return isSat;
        }

        /// <summary>
        /// Adds new units o lambda, while validating the non-existance of conflicts
        /// Returns "true" if no conflict is detected,
        /// "false" otherwise - case in which lambda is being restored to it entry/original values
        /// Execution complexity: O(lambda.Count) * O(FindUnits) =  O(n)
        /// </summary>
        /// <param name="Xk"></param>
        /// <returns></returns>
        private static bool GetUnits(int Xk)
        {
            stats_get_units_cnt++;
            List<int> cpy = lambda.ToList();
            bool isSat = true;
            int unit = 0;
            int opp_unit = 0;
            List<int> new_units = new List<int>();
            if (lambda.Count > 1)
            {
                FindUnits(Xk, new_units);
                while (new_units.Count > 0 && isSat)
                {
                    //pick the first unit in line
                    unit = new_units[0];
                    opp_unit = Opposite(unit);
                    if (!lambda.Contains(opp_unit) && !new_units.Contains(opp_unit))
                    {
                        //and if there is no collision then insert it to lambda
                        lambda.Insert(0, unit);
                        new_units.Remove(unit);
                        //then use that unit to search for more
                        FindUnits(unit, new_units);
                    }
                    else
                    {
                        //a collision was detected because either lambda or new_units list contains the Opposite(unit)
                        isSat = false;
                        lambda = cpy.ToList();
                    }
                }
            }
            IncrementComplexity(lambda.Count);
            return isSat;
        }

        /// <summary>
        /// The basic function of finding Units
        /// It retains and returns all literals found having this property, into "units" list
        /// Complexity O(1) ( or O(sigma(Xk))
        /// </summary>
        /// <param name="Xk"></param>
        /// <param name="units"></param>
        private static void FindUnits(int Xk, List<int> units)
        {
            stats_find_units_cnt++;
            int val_b = 0;
            int val_c = 0;

            for (int i = 0; i < adj_opp[Xk].Count; i += 2)
            {
                val_b = adj_opp[Xk][i];
                val_c = adj_opp[Xk][i + 1];
                if (lambda.Contains(Opposite(val_b)) && !lambda.Contains(val_c) && !units.Contains(val_c))
                    units.Add(val_c);
                if (lambda.Contains(Opposite(val_c)) && !lambda.Contains(val_b) && !units.Contains(val_b))
                    units.Add(val_b);
            }
            IncrementComplexity(adj_opp[Xk].Count);
        }

        /// <summary>
        /// Selects a new header to rerun engine based on it, in case lambda goes to zero elements
        /// In case all headers have been used, it returns false (basically phi is NON-SAT)
        /// Execution complexity O(1)
        /// </summary>
        /// <param name="Xk"></param>
        /// <returns></returns>
        private static bool IncrementHeader(ref int Xk)
        {
            bool isSat = header.Count((bool p) => p) != 2 * n;
            //if not all literals have been used as headers
            if (isSat)
            {
                //pick the next unused literal
                while (header[starting_Xk]) starting_Xk = starting_Xk % (2 * n) + 1;
                header[starting_Xk] = true;
                Xk = starting_Xk;
                lambda.Add(Xk);
            }
            return isSat;
        }

        /// <summary>
        /// Returns the opposite value of a literal
        /// </summary>
        /// <param name="k"></param>
        /// <returns></returns>
        private static int Opposite(int k)
        {
            return (k > n) ? (k - n) : (k + n);
        }

        #endregion engine

        #region utils & stats

        /// <summary>
        /// Methods in this region are used for the following tasks:
        /// - Init of variable
        /// - Formula loading from the .cnf file
        /// - Stats displaying and logging
        /// - Certify a solution
        /// </summary>
        /// <returns></returns>

        private static bool ValidateSolution(Stopwatch stw)
        {
            bool isSat = lambda.Count == n;

            if (statsRecordRun)
                SaveRunHistory();
            lambda.Sort();
            complexity_order = double.Parse(String.Format("{0:0.0000}", Math.Log(complexity_counter, n)));
            if (isSat)
            {
                isSat = CertifySolution(stw.ElapsedMilliseconds);
            }
            if (!isSat)
            {
                PrintStats(isSat, stw.ElapsedMilliseconds);
                Console.ForegroundColor = ConsoleColor.Green;
            }
            return isSat;
        }

        /// <summary>
        /// Logging the statistics info
        /// </summary>
        private static void SaveRunHistory()
        {
            StreamWriter sw = new StreamWriter("run_" + currentFormula + DateTime.Now.Millisecond + ".csv");
            sw.WriteLine("Size(lambda)   ," + "Xj ," + "Xk");
            for (int l = 0; l < stats_lambda_size_history.Count; l++)
                sw.WriteLine(stats_lambda_size_history[l] + "," + (stats_lambda_Xj_history[l] > n ? n - stats_lambda_Xj_history[l] : stats_lambda_Xj_history[l]) + "," + (stats_lambda_Xk_history[l] > n ? n - stats_lambda_Xk_history[l] : stats_lambda_Xk_history[l]));
            sw.Close();
        }

        /// <summary>
        /// Runs the engine over the formula using the different switches:
        /// "all" - all the .cnf files found in its directory will run sequentially
        /// "exh" - all inputs on all polarities will be used to start the engine
        /// "stp" - exection will stop once a NON-SAT solution is found, and it is basically used together with "exh" switch is used
        /// "sol" - will display the solution found on the cmdline window (only the positive polarities)
        /// "rec" - adding extra info into the logs such as lambda size, header, etc
        /// </summary>
        private static void RunFormulae()
        {
            double stats_max_complexity = 0.0;
            int max_complexity_literal = 0;
            double stats_min_complexity = 100.0;
            int min_complexity_literal = 0;
            int solutions_cnt = 0;
            int formula_cnt = 1;
            double stats_total_complexity = 0.0;
            List<List<int>> solutions_list = new List<List<int>>();

            results_dir = "results_dir";
            PrintHeader();
            if (runAll)
                results += "results_all_run_of_" + DateTime.Now.Day + "_" + DateTime.Now.Month + "_" + DateTime.Now.Year + "_" + DateTime.Now.Hour + "_" + DateTime.Now.Minute + "_" + DateTime.Now.Second + ".csv";
            else
                results = currentFormula + DateTime.Now.Day + "_" + DateTime.Now.Month + "_" + DateTime.Now.Year + "_" + DateTime.Now.Hour + "_" + DateTime.Now.Minute + "_" + DateTime.Now.Second + "_results.csv";

            List<string> formulaeFiles = new List<string>();
            if (runAll)
                formulaeFiles = Directory.EnumerateFiles(".").ToList();
            else
                formulaeFiles.Add(currentFormula);

            foreach (string satFormula in formulaeFiles)
            {
                currentFormula = satFormula;
                if (!satFormula.EndsWith(".cnf"))
                    continue;
                else
                    ReadCNF(satFormula);

                Console.ForegroundColor = ConsoleColor.Cyan;
                Console.Write(formula_cnt + ")");

                PrintBar(15);
                Console.ForegroundColor = ConsoleColor.Cyan;
                Console.Write(DateTime.Now.ToString());
                PrintBar(42);

                formula_cnt++;
                stats_max_complexity = 0.0;
                max_complexity_literal = 0;
                stats_min_complexity = 100.0;
                min_complexity_literal = 0;
                solutions_cnt = 0;
                solutions_list = new List<List<int>>();
                stats_total_complexity = 0.0;

                for (int i = 1; i <= 2 * n; i++)
                {
                    ResetStatesHistory();
                    starting_Xk = i;
                    Console.ForegroundColor = ConsoleColor.Cyan;
                    Console.Write(currentFormula);
                    PrintBar(77);
                    string lit = starting_Xk > n ? "-X" + (starting_Xk - n) : " X" + starting_Xk;
                    Console.Write(lit);
                    PrintBar(96);
                    lambda = new List<int>();
                    complexity_counter = 0.0;
                    complexity_order = 0.0;
                    if (RunEngine(starting_Xk))
                    {
                        if (complexity_order > stats_max_complexity)
                        {
                            stats_max_complexity = complexity_order;
                            max_complexity_literal = starting_Xk;
                        }
                        if (complexity_order < stats_min_complexity)
                        {
                            stats_min_complexity = complexity_order;
                            min_complexity_literal = starting_Xk;
                        }
                        if (solutions_cnt == 0)
                        {
                            solutions_cnt++;
                            solutions_list.Add(lambda);
                        }
                        else
                        {
                            bool new_solution = false;
                            foreach (List<int> solution in solutions_list)
                            {
                                foreach (int literal in lambda)
                                    if (!solution.Contains(literal))
                                    {
                                        new_solution = true;
                                        solutions_list.Add(lambda);
                                        solutions_cnt++;
                                        break;
                                    }
                                if (new_solution)
                                    break;
                            }
                        }
                    }
                    else
                    {
                        if (stopOnFailure)
                            Console.ReadLine();

                        if (complexity_order > stats_max_complexity)
                        {
                            stats_max_complexity = complexity_order;
                            max_complexity_literal = starting_Xk;
                        }
                        if (complexity_order < stats_min_complexity)
                        {
                            stats_min_complexity = complexity_order;
                            min_complexity_literal = starting_Xk;
                        }
                    }
                    stats_total_complexity += complexity_counter;
                    if (displaySolution && lambda.Count > 0)
                    {
                        int cnt = 0;
                        Console.WriteLine("Solution: ");
                        for (int j = 0; j < n; j++)
                        {
                            if (lambda[j] <= n)
                            {
                                Console.Write(lambda[j] + " ");
                                if (++cnt % 10 == 0)
                                    Console.WriteLine();
                            }
                        }
                        Console.WriteLine();
                    }
                    if (!exhaustive)
                        break;
                    else
                    {
                        PrintBar(15);
                        Console.ForegroundColor = ConsoleColor.Cyan;
                        Console.Write(DateTime.Now.ToString());
                        PrintBar(42);
                    }
                }
                if (exhaustive)
                {
                    stats_total_complexity = double.Parse(String.Format("{0:0.0000}", (double)Math.Log(stats_total_complexity, n)));

                    string solutions_msg = "";
                    if (solutions_cnt > 0)
                        solutions_msg = "Distinct solutions found: " + solutions_cnt + ", worst case O(n^";
                    else
                        solutions_msg = "No solutions found,  worst case O(n^";

                    string max_lit = max_complexity_literal > n ? (n - max_complexity_literal).ToString() : max_complexity_literal.ToString();
                    string min_lit = min_complexity_literal > n ? (n - min_complexity_literal).ToString() : min_complexity_literal.ToString();
                    Console.WriteLine(solutions_msg + stats_max_complexity + ") on literal " + max_lit + ", best case O(n^" + stats_min_complexity + ") on literal " + min_lit);

                    ConsoleColor foregroundColor = Console.ForegroundColor;
                    Console.ForegroundColor = ConsoleColor.Yellow;
                    Console.WriteLine("Total execution complexity O(n^" + stats_total_complexity + ")");
                    Console.ForegroundColor = foregroundColor;
                    PrintHeader();
                }
            }
        }

        /// <summary>
        /// Init the visited states history hash table
        /// </summary>
        private static void ResetStatesHistory()
        {
            history = new Hashtable(n / 2);
        }

        /// <summary>
        /// Pretty-print on the cmd window
        /// </summary>
        private static void PrintHeader()
        {
            Console.WindowWidth = 190;
            Console.ForegroundColor = ConsoleColor.White;
            string sep_line = "------------------------------------------|----------------------------------|------------------|---------------|------------------|----------------|-----------------------|------------------";
            string hdr = "Formula Number |    Start Time            |        Formula File Name         | Starting Literal |Complexity (n^)|   CPU Time (ms)  | Visited States |   End Time            | Solution     ";
            Console.WriteLine(sep_line);
            Console.WriteLine(hdr);
            Console.WriteLine(sep_line);
        }

        /// <summary>
        /// Adds info to the stats lists
        /// Statistics purposes only
        /// </summary>
        /// <param name="stw"></param>
        /// <param name="isSat"></param>
        /// <param name="Xk"></param>
        private static void UpdateStats(int Xk)
        {
            stats_lambda_Xk_history.Add(Xk);
            stats_lambda_size_history.Add(lambda.Count);
            stats_lambda_Xj_history.Add(lambda.Count > 0 ? lambda.First() : 0);
            stats_main_loop_cnt++;
        }

        /// <summary>
        /// Builds a list of adjacent literals, for each opposite literal
        /// Ex: if literal = 1 and n=100 then it builds the list of adjacent literals for literal 101 (-1)
        /// </summary>
        /// <param name="adj"></param>
        private static void GetNegativeAssoc(List<int>[] adj)
        {
            adj_opp = new List<int>[2 * n + 1];
            for (int i = 1; i <= 2 * n; i++)
            {
                adj_opp[i] = new List<int>();
                int literal = ((i > n) ? (i - n) : (i + n));
                foreach (int item2 in adj[literal])
                {
                    adj_opp[i].Add((item2 < 0) ? (n - item2) : item2);
                }
                List<int> adj1 = new List<int>();
                List<int> adj2 = new List<int>();
                for (int j = 0; j < adj_opp[i].Count; j += 2)
                {
                    adj1.Add(adj_opp[i][j]);
                    adj2.Add(adj_opp[i][j + 1]);
                }
                adj_opp[i].Clear();
                for (int k = 0; k < adj1.Count; k++)
                {
                    int val = adj1[k];
                    int item = ((val > n) ? (val - n) : (val + n));
                    if (adj1.Contains(item))
                    {
                        int num3 = val;
                        adj1[k] = adj2[k];
                        adj2[k] = val;
                    }
                    val = adj2[k];
                    item = ((val > n) ? (val - n) : (val + n));
                    if (adj2.Contains(item))
                    {
                        int num4 = val;
                        adj2[k] = adj1[k];
                        adj1[k] = val;
                    }
                }
                for (int l = 0; l < adj1.Count; l++)
                {
                    adj_opp[i].Add(adj1[l]);
                    adj_opp[i].Add(adj2[l]);
                }
            }
        }

        /// <summary>
        ///Solution certification
        /// </summary>
        /// <param name="dCPURunTimeMs"></param>
        /// <returns></returns>
        private static bool CertifySolution(double dCPURunTimeMs)
        {
            bool isSat = false;
            BuildSolution();
            complexity_order = double.Parse(String.Format("{0:0.0000}", Math.Log(complexity_counter, n)));
            isSat = CheckBinarySolution();
            PrintStats(isSat, dCPURunTimeMs);
            return isSat;
        }

        /// <summary>
        /// Validates that lambda contains a solution for phi
        /// </summary>
        /// <returns></returns>
        private static bool CheckBinarySolution()
        {
            //conditions for a formula to be SAT:
            //1. lambda must contain exactly n elements
            //2. NO literal AND its opposite polarity literal cannot be part of lambda
            //a. validated by the logic of the algorithm before reaching this point
            //b. re-validated here, just in case...
            //3. each clause in the formula must have at least one member in lambda in order for the clause to be satisfied

            //condition 1
            bool isSat = lambda.Count == n;

            //condition 2
            if (isSat)
                foreach (int literal in lambda)
                    if (lambda.Contains(Opposite(literal)))
                        isSat = false;

            if (isSat)
            {
                List<int> list = new List<int>();
                int satisfied_clauses = 0;

                foreach (int item in lambda)
                    list.Add((item > n) ? (n - item) : item);
                list.Sort();
                for (int i = 0; i < m; i++)
                    if (list.Contains(a[i]) || list.Contains(b[i]) || list.Contains(c[i]))
                        satisfied_clauses++;

                //condition 3
                isSat = satisfied_clauses == m;
            }
            return isSat;
        }

        /// <summary>
        /// increments the complexity counter
        /// </summary>
        /// <param name="inc"></param>
        private static void IncrementComplexity(int inc)
        {
            complexity_counter += inc;
        }

        /// <summary>
        /// Builds the final soluion based on the lambda
        /// Then sorts it following column "a"
        /// Logging purposes only
        /// </summary>
        private static void BuildSolution()
        {
            foreach (int item in lambda)
            {
                int num = ((item > n) ? (n - item) : item);
                for (int i = 0; i < m; i++)
                {
                    if (a[i] != num)
                    {
                        if (b[i] == num)
                        {
                            Swap(a, b, i);
                        }
                        else if (c[i] == num)
                        {
                            Swap(a, c, i);
                        }
                    }
                }
            }
            VerticalSort();
        }

        /// <summary>
        /// Pretty-printing purposes only
        /// </summary>
        /// <param name="pos"></param>
        private static void PrintBar(int pos)
        {
            Console.WindowWidth = 190;
            Console.CursorLeft = pos;
            Console.ForegroundColor = ConsoleColor.White;
            Console.Write("| ");
            Console.ForegroundColor = ConsoleColor.Green;
        }

        /// <summary>
        /// Displays the statistics after an engine run
        /// </summary>
        /// <param name="isSat"></param>
        /// <param name="dCPURunTimeMs"></param>
        private static void PrintStats(bool isSat, double dCPURunTimeMs)
        {
            double complexityOrder = double.Parse(String.Format("{0:0.0000}", Math.Log(complexity_counter, n)));
            Console.Write(complexityOrder);
            PrintBar(112);
            Console.Write(dCPURunTimeMs);
            PrintBar(131);
            Console.Write(history.Count);
            PrintBar(148);
            Console.Write(DateTime.Now.ToString());
            PrintBar(172);
            if (!isSat)
                Console.ForegroundColor = ConsoleColor.Red;
            Console.WriteLine(isSat ? " SAT" : " NON-SAT");

            StreamWriter sw;

            if (!File.Exists(results))
            {
                sw = new StreamWriter(results, append: true);
                sw.Write("File Name,");
                sw.Write("n,");
                sw.Write("m,");
                sw.Write("Base Value,");
                sw.Write("CPU Time(ms) ,");
                sw.Write("Complexity Order n^,");
                sw.Write("Total Hits,");
                sw.Write("Main Loop O(n^),");
                sw.Write("Hits/Loop O(n^),");
                sw.Write("GetOppUnits,");
                sw.Write("GetUnits,");
                sw.Write("FindUnits,");
                sw.WriteLine("Solution");
                sw.Close();
            }

            sw = new StreamWriter(results, append: true);
            sw.Write(currentFormula + ",");
            sw.Write(n + ",");
            sw.Write(m + ",");
            sw.Write(stats_base_literal + ",");
            sw.Write(dCPURunTimeMs + ", ");
            sw.Write(complexityOrder + ",");
            sw.Write(complexity_counter + ",");
            sw.Write(String.Format("{0:0.0000}", Math.Log((double)stats_main_loop_cnt, n)) + ",");
            sw.Write(String.Format("{0:0.0000}", Math.Log(complexity_counter / (double)stats_main_loop_cnt, n)) + ",");
            sw.Write(stats_get_opp_units_cnt + ",");
            sw.Write(stats_get_units_cnt + ",");
            sw.Write(stats_find_units_cnt + ",");

            if (isSat)
            {
                foreach (int k in lambda)
                    if (k <= n) sw.Write(k + " ");
            }
            else
                sw.Write("NON SAT");

            sw.WriteLine();
            sw.Close();
            if (!Directory.Exists(results_dir))
                Directory.CreateDirectory(results_dir);

            sw = new StreamWriter(results_dir + "\\" + currentFormula + ".txt");
            if (isSat)
            {
                for (int m = 0; m < a.Length; m++)
                    sw.WriteLine(a[m] + ", " + b[m] + ", " + c[m]);

                sw.Write("Runtime (ms): " + dCPURunTimeMs + ", O(n^" + complexityOrder + ")  ");
            }
            else
            {
                sw.WriteLine("NON SAT,Runtime(ms): " + dCPURunTimeMs + ", O(n^" + complexityOrder + "),");
            }
            sw.Close();
        }

        /// <summary>
        /// Load and parse the .cnf file
        /// </summary>
        /// <param name="satFormula"></param>
        private static void ReadCNF(string satFormula)
        {
            StreamReader streamReader = new StreamReader(satFormula);
            string text = streamReader.ReadToEnd();
            string[] array = new string[6];
            int startIndex = text.IndexOf("p cnf") + 5;
            string text2 = text.Substring(startIndex);
            string text3 = text2.Substring(0, text2.IndexOf('\n'));
            string[] array2 = text3.Split(' ');
            n = 0;
            m = 0;
            for (int i = 0; i < array2.Length; i++)
            {
                if (array2[i].Trim().Length > 0)
                {
                    if (n != 0)
                    {
                        m = int.Parse(array2[i]);
                        break;
                    }
                    n = int.Parse(array2[i]);
                }
            }
            text2 = text2.Substring(text2.IndexOf('\n') + 1);
            string[] separator = new string[1]
            {
                "\n"
            };
            string[] tmp_clauses = new string[m];
            string[] array3 = text2.Split(separator, StringSplitOptions.None);
            int index = 0;
            foreach (string s in array3)
            {
                if (s.Trim().Length >= 3)
                {
                    tmp_clauses[index++] = s.Trim();
                }
            }
            array3 = tmp_clauses.ToArray();
            a = new int[m];
            b = new int[m];
            c = new int[m];

            for (int j = 0; j < m; j++)
            {
                int num = 0;
                string text4 = array3[j].Trim();

                array = text4.Split(' ');
                for (int k = 0; k < array.Length; k++)
                {
                    if (array[k].Trim().Length <= 0)
                    {
                        continue;
                    }
                    if (num == 0)
                    {
                        a[j] = int.Parse(array[k]);
                    }
                    else
                    {
                        if (num != 1)
                        {
                            c[j] = int.Parse(array[k]);
                            break;
                        }
                        b[j] = int.Parse(array[k]);
                    }
                    num++;
                }
                if (a[j] == 0)
                {
                    break;
                }
                if (b[j] == 0)
                {
                    b[j] = a[j];
                }
                if (c[j] == 0)
                {
                    c[j] = b[j];
                }
            }
            Init();
        }

        /// <summary>
        /// Init the lists containing the adjacent literals for each input/literal
        /// </summary>
        private static void Init()
        {
            List<int>[] adj = new List<int>[2 * n + 1]; ;
            for (int j = 1; j <= n; j++)
            {
                adj[j] = new List<int>();
                adj[j + n] = new List<int>();
            }
            for (int k = 0; k < m; k++)
            {
                if (a[k] > 0)
                {
                    adj[a[k]].Add(b[k]);
                    adj[a[k]].Add(c[k]);
                }
                else
                {
                    adj[-a[k] + n].Add(b[k]);
                    adj[-a[k] + n].Add(c[k]);
                }
                if (b[k] > 0)
                {
                    adj[b[k]].Add(a[k]);
                    adj[b[k]].Add(c[k]);
                }
                else
                {
                    adj[-b[k] + n].Add(a[k]);
                    adj[-b[k] + n].Add(c[k]);
                }
                if (c[k] > 0)
                {
                    adj[c[k]].Add(a[k]);
                    adj[c[k]].Add(b[k]);
                }
                else
                {
                    adj[-c[k] + n].Add(a[k]);
                    adj[-c[k] + n].Add(b[k]);
                }
            }

            GetNegativeAssoc(adj);
        }

        /// <summary>
        /// Init the stats variables
        /// </summary>
        private static void InitStats()
        {
            stats_lambda_size_history = new List<long>();
            stats_lambda_Xj_history = new List<long>();
            stats_lambda_Xk_history = new List<long>();
            stats_main_loop_cnt = 0uL;
            stats_get_opp_units_cnt = 0uL;
            stats_get_units_cnt = 0uL;
            stats_find_units_cnt = 0uL;
            stats_base_literal = 0;
        }

        private static void Swap(int[] a1, int[] b1, int i)
        {
            int num = a1[i];
            a1[i] = b1[i];
            b1[i] = num;
        }

        /// <summary>
        /// Sort by column "a" - only for logging purposes
        /// </summary>
        private static void VerticalSort()
        {
            List<int> list_a = new List<int>();
            List<int> list_b = new List<int>();
            List<int> list_c = new List<int>();
            for (int i = 0; i <= n; i++)
            {
                int num = i;
                for (int j = 0; j < a.Count(); j++)
                {
                    if (a[j] == num || (a[j] == -num && a[j] != 0))
                    {
                        list_a.Add(a[j]);
                        list_b.Add(b[j]);
                        list_c.Add(c[j]);
                    }
                }
            }
            list_a.CopyTo(a);
            list_b.CopyTo(b);
            list_c.CopyTo(c);
        }

        #endregion utils & stats
    }
}