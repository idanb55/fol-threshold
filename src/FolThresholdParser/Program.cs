using System;
using System.IO;
using System.Linq;
using CommandLine;
using FolThresholdParser.FolThresholdSystem;
using FolThresholdParser.Parser;
using FolThresholdParser.Utils;

namespace FolThresholdParser
{
    public class Options
    {
        [Option('v', "verbose", Required = false, HelpText = "Set output to verbose messages.")]
        public bool Verbose { get; set; }

        [Option('o', "output-dir", Required = true, HelpText = "Output directory")]
        public string OutputDir { get; set; }

        [Option('f', "input", Required = true, HelpText = "Threshold specification file")]
        public string TresholdSpecFilePath { get; set; }

        [Option('c', "cvc", Required = false, HelpText = "CVC4 solver path", Default = "cvc4-1.6-win64-opt.exe")]
        public string Cvc4Path { get; set; }

        [Option('a', "auto-conjecture", Required = false, HelpText = "Automatically produce conjectures to file")]
        public string AutoConjectureOutput { get; set; }

        [Option('n', "auto-conjecture-count", Required = false, HelpText = "Number of conjectures to try")]
        public int AutoConjectureCount { get; set; }
    }

    public class Program
    {
        public static Options Options;

        public static void Main(string[] args)
        {
            try
            {
                CommandLine.Parser.Default.ParseArguments<Options>(args)
                    .WithParsed(Run)
                    .WithNotParsed(errs => { });
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex.Message);
            }
        }

        private static void Run(Options opts)
        {
            Options = opts;

            Console.WriteLine("= Welcome to Fol Threshold Parser!");
            Console.WriteLine($"= Reading threshold file {opts.TresholdSpecFilePath}");

            var system = new FolThresholdSystem.FolThresholdSystem();
            foreach (var t in Tokenizer.Tokenize(opts.TresholdSpecFilePath))
            {
                var arr = t.ToArray();
                if(opts.Verbose) Console.WriteLine($"++ {arr.FirstOrDefault()?.Code}");
                system.ParseCode(arr);
            }

            Console.WriteLine("= Success");

            if (Directory.Exists(opts.OutputDir)) Directory.Delete(opts.OutputDir, true);
            Directory.CreateDirectory(opts.OutputDir);

            var ivyPath = Path.Combine(opts.OutputDir, "ivy.ivy");
            File.AppendAllLines(ivyPath, system.ToIvyAxioms());
            Console.WriteLine($"= IVY output file created: {ivyPath}");

            var counter = 0;
            foreach (var specification in system.Formulas.Where(spec => spec.Conjecture))
            {
                var smtFile = Path.Combine(opts.OutputDir, $"threshold_conjecture{counter:D5}.smt2");
                File.AppendAllLines(smtFile,
                    system.AssertThresholdSmt2(specification));
                Console.WriteLine($"== SMT file created: {smtFile} : {specification.Formula}");
                counter++;
            }

            if (string.IsNullOrEmpty(opts.AutoConjectureOutput)) return;

            Console.WriteLine("= Starting producing conjectures");
            counter = 0;
            using (var ps = new ProgressBar(opts.AutoConjectureCount))
            {
                foreach (var specification in system.ProduceConjectures().Take(opts.AutoConjectureCount).Verify(system, ps))
                {
                    var resultThresholdPath = Path.Combine(opts.OutputDir, opts.AutoConjectureOutput);

                    File.AppendAllLines(resultThresholdPath, new[] {specification.ToString()});
                    counter++;
                }
            }

            Console.WriteLine("= Success");
        }
    }
}
