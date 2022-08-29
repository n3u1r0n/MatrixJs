var eps = 10e-15;

class Matrix extends Array {
  constructor (...elements) {
    if (!elements instanceof Array) throw 'Matrix expects arrays with same length of numerical type.';
    var m = elements.length;
    var n = null;
    for (var i = 0; i < m; i++) {
      if (!elements[i] instanceof Array) throw 'Matrix expects arrays with same length of numerical type.';
      if (n && n != elements[i].length) throw 'Matrix expects arrays with same length of numerical type.';
      n = elements[i].length;
      for (var j = 0; j < n; j++) {
        if (typeof(elements[i][j]) != 'number') throw 'Matrix expects arrays with same length of numerical type.';
      }
    }
    super(...elements);
    this.m = m;
    this.n = n;
  }
  add (other) {
    if (!other instanceof Array && typeof(other) != 'number') throw 'Must add matrix or number.';
    if (other instanceof Array && (this.m != other.m || this.n != other.n)) throw 'Matrix to add must have same shape.';
    if (typeof(other) == 'number' && this.m != this.n) throw 'Matrix must be a square matrix to add a number.';
    var elements = [];
    if (typeof(other) == 'number') {
      for (var i = 0; i < this.m; i++) {
        var row = [];
        for (var j = 0; j < this.n; j++) {
          row.push(this[i][j] + other * (i == j));
        }
        elements.push(row);
      }
    } else {
      for (var i = 0; i < this.m; i++) {
        var row = [];
        for (var j = 0; j < this.n; j++) {
          row.push(this[i][j] + other[i][j]);
        }
        elements.push(row);
      }
    }
    var result = new Matrix(...elements);
    if (result.n == 1) {
      return new Vector(...result.T[0]);
    }
    return result;
  }
  sub (other) {
    if (!other instanceof Array && typeof(other) != 'number') throw 'Must subtract matrix or number.';
    if (other instanceof Array && (this.m != other.m || this.n != other.n)) throw 'Matrix to subtract must have same shape.';
    if (typeof(other) == 'number' && this.m != this.n) throw 'Matrix must be a square matrix to subtract a number.';
    var elements = [];
    if (typeof(other) == 'number') {
      for (var i = 0; i < this.m; i++) {
        var row = [];
        for (var j = 0; j < this.n; j++) {
          row.push(this[i][j] - other * (i == j));
        }
        elements.push(row);
      }
    } else {
      for (var i = 0; i < this.m; i++) {
        var row = [];
        for (var j = 0; j < this.n; j++) {
          row.push(this[i][j] - other[i][j]);
        }
        elements.push(row);
      }
    }
    var result = new Matrix(...elements);
    if (result.n == 1) {
      return new Vector(...result.T[0]);
    }
    return result;
  }
  mul (other, _rec = true) {
    if (!other instanceof Array && typeof(other) != 'number') throw 'Must multiply with matrix or number.';
    if (other instanceof Array && this.n != other.m) throw 'Matrix shapes do not match for multiplication.';
    var elements = [];
    if (typeof(other) == 'number') {
      for (var i = 0; i < this.m; i++) {
        var row = [];
        for (var j = 0; j < this.n; j++) {
          row.push(this[i][j] * other);
        }
        elements.push(row);
      }
      var result = new Matrix(...elements);
      result._det = (this?._det != undefined) ? this._det * other ** this.m : undefined;
      result._inv = (this?._inv != undefined) ? this._inv.mul(1 / other) : undefined;
    } else {
      for (var i = 0; i < this.m; i++) {
        var row = [];
        for (var j = 0; j < other.n; j++) {
          var result = 0;
          for (var k = 0; k < this.n; k++) {
            result += this[i][k] * other[k][j];
          }
          row.push(result);
        }
        elements.push(row);
      }
      var result = new Matrix(...elements);
      result._det = (this?._det != undefined && other?._det != undefined) ? this._det * other._det : undefined;
      result._inv = (this?._inv != undefined && other?._inv != undefined && _rec) ? other._inv.mul(this._inv, false) : undefined;
    }
    if (result.n == 1) {
      return new Vector(...result.T[0]);
    }
    return result;
  }
  row (i) {
    return new Vector(...this[i]);
  }
  col (j) {
    var elements = [];
    for (var i = 0; i < this.m; i++) {
      elements.push(this[i][j]);
    }
    return new Vector(...elements);
  }
  get T () {
    if (this?._T != undefined) return this._T;
    this._T = [];
    for (var i = 0; i < this.n; i++) {
      var row = [];
      for (var j = 0; j < this.m; j++) {
        row.push(this[j][i]);
      }
      this._T.push(row);
    }
    this._T = new Matrix(...this._T);
    this._T._det = this?._det;
    this._T._inv = this?._inv?.T;
    return this._T;
  }
  get QR () {
    if (this.m < this.n) throw 'Matrix has wrong shape for QR decomposition.';
    if (this?._Q != undefined && this?._R != undefined) return [this._Q, this._R];
    var R = this.mul(Matrix.identity(this.n));
    var Q = Matrix.identity(this.m);
    for (var r = 0; r < this.n; r++) {
      var col = R.col(r);
      for (var s = 0; s < r; s++) {
        col[s] = [0];
      }
      if (!col.is_base_vector(r)) {
        let alpha = (col[r][0] < 0 ? 1 : -1)  * col.norm();
        let a = col.sub(Vector.e(r, this.m).mul(alpha));
        let H = Matrix.identity(a.m).sub(a.mul(a.T).mul(2 / a.norm2()));
        H._det = -1;
        H._inv = new Matrix(...H)
        Q = Q.mul(H);
        R = H.mul(R);
      }
      for (let s = r + 1; s < this.m; s++) {
        R[s][r] = 0;
      }
    }
    this._Q = Q;
    this._R = R;
    return [Q, R];
  }
  get det () {
    if (this?._det != undefined) return this._det;
    if (this.m != this.n) {
      this._det = 0;
      return 0;
    }
    this._det = this.QR[0].det;
    for (var i = 0; i < this.m; i++) {
      this._det *= this.QR[1][i][i] * (abs(this.QR[1][i][i]) > eps);
    }
    return this._det;
  }
  static ones (m, n) {
    var elements = [];
    for (var i = 0; i < m; i++) {
      elements.push(new Array(n).fill(1));
    }
    var result = new Matrix(...elements);
    result._det = 0;
    return result;
  }
  static zeros (m, n) {
    var elements = [];
    for (var i = 0; i < m; i++) {
      elements.push(new Array(n).fill(0));
    }
    var result = new Matrix(...elements);
    result._det = 0;
    return result;
  }
  static identity (n) {
    var elements = [];
    for (var i = 0; i < n; i++) {
      var row = [];
      for (var j = 0; j < n; j++) {
        row.push(int(i == j));
      }
      elements.push(row);
    }
    var result = new Matrix(...elements);
    result._det = 1;
    result._inv = new Matrix(...elements);
    result._T = new Matrix(...elements);
    return result;
  }
  static permutation (i, j, n) {
    var elements = [];
    for (var k = 0; k < n; k++) {
      var row = [];
      for (var l = 0; l < n; l++) {
        row.push(int((k == l && k != i && k != j) || (k == i && l == j) || (k == j && l == i)));
      }
      elements.push(row);
    }
    var result = new Matrix(...elements);
    result._det = -1;
    result._inv = new Matrix(...elements);
    result._T = new Matrix(...elements);
    return result;
  }
  static random(m, n) {
    var elements = [];
    for (var i = 0; i < m; i++) {
      var row = [];
      for (var j = 0; j < n; j++) {
        row.push(Math.random());
      }
      elements.push(row);
    }
    var result = new Matrix(...elements);
    return result;
  }
}


class Vector extends Matrix {
  constructor (...elements) {
    for (let i = 0; i < elements.length; i++) {
      elements[i] = [elements[i]];
    }
    super(...elements);
  }
  inner (other) {
    var result = 0;
    for (let i = 0; i < this.m; i++) {
      result += this[i][0] * other[i][0];
    }
    return result;
  }
  norm2 () {
    var result = 0;
    for (let i = 0; i < this.m; i++) {
      result += this[i][0] ** 2;
    }
    return result;
  }
  norm () {
    return Math.sqrt(this.norm2());
  }
  is_base_vector(i) {
    for (let j = 0; j < this.m; j++) {
      if (i != j && abs(this[j]) > eps) {
        return false;
      }
    }
    return this[i] != [0];
  }
  static e (i, n) {
    var elements = [];
    for (var j = 0; j < n; j++) {
      elements.push(int(j == i));
    }
    return new Vector(...elements)
  }
}
