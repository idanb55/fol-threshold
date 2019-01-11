using System;
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
                var system = new FolThresholdSystem();
                foreach (var t in Tokenizer.Tokenize("..\\..\\..\\..\\..\\bosco2.folthreshold"))
                {
                    system.ParseCode(t.ToArray());
                }

                var ocamlBapaString = system.ToString();
                Console.WriteLine(ocamlBapaString);
                Console.WriteLine();
                foreach (var ivyAxiom in system.ToIvyAxioms())
                {
                    Console.WriteLine(ivyAxiom);
                }

                foreach (var bapaSetExpression in VennDiagram.VennDiagramIterator.GetVennZonesHelper(new []
                {
                    new SetVarExpression("A1"), new SetVarExpression("B1"), new SetVarExpression("C1"),
                }))
                {
                    Console.WriteLine(bapaSetExpression);
                    Console.Read();
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex);
            }

            Console.Read();
        }
    }
}
