using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using FolThresholdParser.FolSyntax;
using FolThresholdParser.Parser;
using FolThresholdParser.Utils;

namespace FolThresholdParser.FolThresholdSystem
{
    public class Specification
    {
        public bool Conjecture;
        public bool NaturalSpec;
        public Formula Formula;

        public static Specification Parse(ArrayView<Token> tokens)
        {
            return new Specification
            {
                Conjecture = tokens[0].Type == SyntaxKind.ConjectureKeyword,
                NaturalSpec = tokens[1].Type == SyntaxKind.NaturalKeyword,
                Formula = tokens[1].Type == SyntaxKind.NaturalKeyword
                    ? NaturalFormula.Parse(tokens.Skip(2))
                    : SetFormula.Parse(tokens.Skip(2))
            };
        }

        public string ToBoundIvyAxiom(Dictionary<string, Identifier> identifiers)
        {
            return Formula.ToBoundIvyAxiomActual(identifiers);
        }

        public override string ToString()
        {
            var conjecture = Conjecture ? "conjecture" : "axiom";
            var type = NaturalSpec ? "natural" : "set";
            return $"{conjecture} {type} {Formula}";
        }
    }
}
