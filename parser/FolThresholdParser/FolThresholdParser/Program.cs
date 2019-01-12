using System;
using System.IO;
using System.Linq;
using FolThresholdParser.FolSyntax;
using FolThresholdParser.Parser;

namespace FolThresholdParser
{
    public class Program
    {
        public static void Main(string[] args)
        {
            try
            {
                var inputFile = @"..\..\..\..\..\bosco2.folthreshold"; 
                var outputDir = $@"..\..\..\..\..\out_{DateTime.Now:yyyy_MM_dd_HH_mm_ss}";

                var system = new FolThresholdSystem.FolThresholdSystem();
                foreach (var t in Tokenizer.Tokenize(inputFile))
                {
                    system.ParseCode(t.ToArray());
                }

                Directory.CreateDirectory(outputDir);
                
                foreach (var ivyAxiom in system.ToIvyAxioms())
                {
                    File.AppendAllLines(Path.Combine(outputDir, "ivy.ivy"), new[] {ivyAxiom});
                }

                foreach (var smtAssert in system.AssertThresholdSmt2())
                {
                    Console.WriteLine(smtAssert);
                    //File.AppendAllLines(Path.Combine(outputDir, "threshold.smt2"), new[] { ivyAxiom });
                }

                /**foreach (var bapaSetExpression in VennDiagram.VennDiagramIterator.GetVennZonesHelper(new []
                {
                    new SetVarExpression("A1"), new SetVarExpression("B1"), new SetVarExpression("C1"),
                }))
                {
                    Console.WriteLine(bapaSetExpression);
                    Console.Read();
                }**/
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex);
            }

            Console.Read();
        }
    }
}
