using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;

namespace FolThresholdParser
{
    public class Tokenizer : IEnumerable<Token>
    {
        public static IEnumerable<IEnumerable<Token>> Tokenize(string filePath)
        {
            return File.ReadLines(filePath).Select((line, count) => new Tokenizer(line, count));
        }            

        public Tokenizer(string code, int line)
        {
            _line = line;

            var commentMatch = CommentRegex.Match(code);
            if (commentMatch.Success) code = code.Substring(0, commentMatch.Index);
            _code = code;
        }

        private readonly string _code;

        private int _cursor;
        private readonly int _line;

        private const string CommentString = "#";
        private static readonly Regex CommentRegex = new Regex(Regex.Escape(CommentString) + ".*");

        private readonly Dictionary<SyntaxKind, Regex> _patterns = new Dictionary<SyntaxKind, Regex>
        {
            {SyntaxKind.VariableNameToken,     new Regex("^[a-zA-Z]+")},            
            {SyntaxKind.LiteralNumberToken,   new Regex("^[0-9]+")   },
            {SyntaxKind.WhitespaceToken,   new Regex("^\\s+")   }
        };

        private static readonly Dictionary<SyntaxKind, string> Keywords = new Dictionary<SyntaxKind, string>
        {
            // keywords
            {SyntaxKind.EmptySetKeyword, "emptyset"},
            {SyntaxKind.GlobalSetKeyword, "globalset"},
            {SyntaxKind.ConstantKeyword, "constant"},
            {SyntaxKind.NaturalKeyword, "natural"},
            {SyntaxKind.QuorumKeyword, "quorum"},
            {SyntaxKind.AxiomKeyword, "axiom"},
            {SyntaxKind.ConjectureKeyword, "conjecture"},
            {SyntaxKind.NonEmptyKeyword, "nonempty"},
            {SyntaxKind.RelationKeyword, "relation"},

            // operation
            { SyntaxKind.OpenParenthesisToken,         ("(")         },
            { SyntaxKind.CloseParenthesisToken,     (")")         },

            { SyntaxKind.PlusOperationToken,          ("+")        },
            { SyntaxKind.MinusOperationToken,         ("-")        },
            { SyntaxKind.AndOperationToken,          ("&")        },
            { SyntaxKind.OrOperationToken,         ("|")        },
            { SyntaxKind.ComplementOperationToken,         ("~")        },

            { SyntaxKind.EqualToken,                 ("==")            },
            { SyntaxKind.InEqualToken,              ("!=")         },

            { SyntaxKind.GeqThanToken,              (">=")         },
            { SyntaxKind.GreaterThanToken,              (">")         },

            { SyntaxKind.LeqThanToken,              ("<=")         },
            { SyntaxKind.LessThanToken,              ("<")         }
            
        };

        private int MatchesConst(SyntaxKind kind)
        {
            var length = Keywords[kind].Length;
            if (_code.Length >= _cursor + length && Keywords[kind].Equals(_code.Substring(_cursor, length))) return length;
            return 0;
        }

        private int MatchesPattern(SyntaxKind kind)
        {
            var match = _patterns[kind].Match(_code.Substring(_cursor));
            return match.Success ? match.Length : 0;
        }

        private Token MakeToken(SyntaxKind kind, int length)
        {
            var res = new Token(_cursor, length, kind, _code, _line);
            _cursor += length;
            return res;
        }

        private Token NextToken()
        {
            foreach (var kind in Keywords.Keys)
            {
                var length = MatchesConst(kind);
                if (length <= 0) continue;
                return MakeToken(kind, length);
            }

            foreach (var kind in _patterns.Keys)
            {
                var length = MatchesPattern(kind);
                if (length <= 0) continue;
                return MakeToken(kind, length);
            }

            throw new CountNotTokenizeCharException(_code, _cursor);            
        }

        public IEnumerable<Token> Tokenize()
        {
            for (_cursor = 0; _cursor < _code.Length;)
            {
                var savedCursor = _cursor;

                var token = NextToken();
                if (token != null && token.Type != SyntaxKind.WhitespaceToken) yield return token;
                                
                if (savedCursor == _cursor)
                    throw new CountNotTokenizeCharException(_code, _cursor);
            }
        }

        public IEnumerator<Token> GetEnumerator()
        {
            return Tokenize().GetEnumerator();
        }

        IEnumerator IEnumerable.GetEnumerator()
        {
            return Tokenize().GetEnumerator();
        }
    }

    [Serializable]
    internal class CountNotTokenizeCharException : Exception
    {
        public CountNotTokenizeCharException(string code, int cursor) : base($"parse error: {code} could not be tokenized on col {cursor} ({code.Substring(cursor)})")
        {
        }
    }
}