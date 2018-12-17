using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;

namespace FolThresholdParser
{
    public struct ArrayView<T> : IEnumerable<T>
    {
        private readonly T[] _array;
        private readonly int _offset;
        private readonly int _length;

        private ArrayView(T[] array, int offset, int length)
        {
            _array = array;
            _offset = offset;
            _length = length;
        }

        public static implicit operator ArrayView<T>(T[] array)
        {
            return new ArrayView<T>(array, 0, array.Length);
        }

        public T this[int index]
        {
            get
            {
                CheckInbound(index);
                return _array[index];
            }
            set
            {
                CheckInbound(index);
                _array[index] = value;
            }
        }

        public int Length => _length;

        private void CheckInbound(int index)
        {
            if (index < 0) throw new IndexOutOfRangeException();
            if (index < _offset) throw new IndexOutOfRangeException();
            if (index > _offset + _length) throw new IndexOutOfRangeException();
            if (index > _array.Length) throw new IndexOutOfRangeException();
        }

        private ArrayView<T> CreateView(int newOffset, int newLength)
        {
            CheckInbound(newOffset);
            CheckInbound(newLength);

            return new ArrayView<T>(_array, newOffset, newLength);
        }

        public ArrayView<T> Substring(int startIndex, int length)
        {
            return CreateView(_offset + startIndex, _offset + startIndex + length);
        }

        public ArrayView<T> Skip(int items)
        {
            return CreateView(_offset + items, _offset + -items);
        }

        public ArrayView<T> Take(int items)
        {
            return CreateView(_offset, items);
        }

        private IEnumerable<T> AsEnumerable()
        {
            return _array.Skip(_offset).Take(_length);
        }

        public IEnumerator<T> GetEnumerator()
        {
            return AsEnumerable().GetEnumerator();
        }

        IEnumerator IEnumerable.GetEnumerator()
        {
            return AsEnumerable().GetEnumerator();
        }
    }
}
