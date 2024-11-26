const path = require('path')

module.exports = {
  entry           : './src/controller.js'
, mode            : 'development'
, output          : {
    filename      : 'controller.js'
  , path          : path.resolve(__dirname, '.')
  , libraryTarget : "var"
  , library       : "Controller"
  },
  devServer: {
    static: ".",
    host: "127.0.0.1",
    port: 3000,
    headers: {
      "Access-Control-Allow-Origin": "http://127.0.0.1",
      "Access-Control-Allow-Methods": "GET, POST, PUT, DELETE, PATCH, OPTIONS",
      "Access-Control-Allow-Headers": "X-Requested-With, content-type, Authorization"
    }
  }
}
