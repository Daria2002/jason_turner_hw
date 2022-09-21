#include <math.h>   // smallpt, a Path Tracer by Kevin Beason, 2008
#include <stdio.h>  //        Remove "-fopenmp" for g++ version < 4.2
#include <stdlib.h> // Make : g++ -O3 -fopenmp smallpt.cpp -o smallpt

// video notes:
// functions
// don't const memeber variables
// don't const_cast
// unsigned short const *xi

struct Vec {        // Usage: time ./smallpt 5000 && xv image.ppm
  double x, y, z;   // position, also color (r,g,b)
  Vec(double x_ = 0, double y_ = 0, double z_ = 0) {
    x = x_;
    y = y_;
    z = z_;
  }
  auto operator+(const auto &b) const { return Vec(x + b.x, y + b.y, z + b.z); }
  auto operator-(const auto &b) const { return Vec(x - b.x, y - b.y, z - b.z); }
  auto operator*(auto b) const { return Vec(x * b, y * b, z * b); }
  auto mult(const auto &b) const { return Vec(x * b.x, y * b.y, z * b.z); }
  auto &norm() { return *this = *this * (1 / sqrt(x * x + y * y + z * z)); }
  auto dot(const auto &b) const {
    return x * b.x + y * b.y + z * b.z;
  } // cross:
  auto operator%(auto &b) {
    return Vec(y * b.z - z * b.y, z * b.x - x * b.z, x * b.y - y * b.x);
  }
};
struct Ray {
  Vec o, d;
  Ray(auto o_, auto d_) : o(o_), d(d_) {}
};
enum Refl_t { DIFF, SPEC, REFR }; // material types, used in radiance()
struct Sphere {
  double rad;  // radius
  Vec p, e, c; // position, emission, color
  Refl_t refl; // reflection type (DIFFuse, SPECular, REFRactive)
  Sphere(auto rad_, auto p_, auto e_, auto c_, auto refl_)
      : rad(rad_), p(p_), e(e_), c(c_), refl(refl_) {}
  double intersect(const auto &r) const { // returns distance, 0 if nohit
    auto op = p - r.o; // Solve t^2*d.d + 2*t*(o-p).d + (o-p).(o-p)-R^2 = 0
    double t;
    auto eps = 1e-4, b = op.dot(r.d), det = b * b - op.dot(op) + rad * rad;
    if (det < 0)
      return 0;
    else
      det = sqrt(det);
    return (t = b - det) > eps ? t : ((t = b + det) > eps ? t : 0);
  }
};
Sphere spheres[] = {
    // Scene: radius, position, emission, color, material
    Sphere(1e5, Vec(1e5 + 1, 40.8, 81.6), Vec(), Vec(.75, .25, .25),
           DIFF), // Left
    Sphere(1e5, Vec(-1e5 + 99, 40.8, 81.6), Vec(), Vec(.25, .25, .75),
           DIFF),                                                     // Rght
    Sphere(1e5, Vec(50, 40.8, 1e5), Vec(), Vec(.75, .75, .75), DIFF), // Back
    Sphere(1e5, Vec(50, 40.8, -1e5 + 170), Vec(), Vec(), DIFF),       // Frnt
    Sphere(1e5, Vec(50, 1e5, 81.6), Vec(), Vec(.75, .75, .75), DIFF), // Botm
    Sphere(1e5, Vec(50, -1e5 + 81.6, 81.6), Vec(), Vec(.75, .75, .75),
           DIFF),                                                      // Top
    Sphere(16.5, Vec(27, 16.5, 47), Vec(), Vec(1, 1, 1) * .999, SPEC), // Mirr
    Sphere(16.5, Vec(73, 16.5, 78), Vec(), Vec(1, 1, 1) * .999, REFR), // Glas
    Sphere(600, Vec(50, 681.6 - .27, 81.6), Vec(12, 12, 12), Vec(),
           DIFF) // Lite
};
inline auto clamp(auto x) { return x < 0 ? 0 : x > 1 ? 1 : x; }
inline auto toInt(auto x) { return int(pow(clamp(x), 1 / 2.2) * 255 + .5); }
inline auto intersect(const auto &r, auto &t, auto &id) {
  auto n = sizeof(spheres) / sizeof(Sphere);
  auto inf = t = 1e20;
  double d;
  for (auto i = int(n); i--;)
    if ((d = spheres[i].intersect(r)) && d < t) {
      t = d;
      id = i;
    }
  return t < inf;
}
auto radiance(const auto &r, auto depth, auto *Xi) {
  double t;   // distance to intersection
  auto id = 0; // id of intersected object
  if (!intersect(r, t, id))
    return Vec();                  // if miss, return black
  const auto &obj = spheres[id]; // the hit object
  auto x = r.o + r.d * t, n = (x - obj.p).norm(),
      nl = n.dot(r.d) < 0 ? n : n * -1, f = obj.c;
  auto p = f.x > f.y && f.x > f.z ? f.x : f.y > f.z ? f.y : f.z; // max refl
  if (++depth > 5)
    if (erand48(Xi) < p)
      f = f * (1 / p);
    else
      return obj.e;       // R.R.
  if (obj.refl == DIFF) { // Ideal DIFFUSE reflection
    auto r1 = 2 * M_PI * erand48(Xi), r2 = erand48(Xi), r2s = sqrt(r2);
    auto w = nl, u = ((fabs(w.x) > .1 ? Vec(0, 1) : Vec(1)) % w).norm(),
        v = w % u;
    auto d = (u * cos(r1) * r2s + v * sin(r1) * r2s + w * sqrt(1 - r2)).norm();
    return obj.e + f.mult(radiance(Ray(x, d), depth, Xi));
  } else if (obj.refl == SPEC) // Ideal SPECULAR reflection
    return obj.e +
           f.mult(radiance(Ray(x, r.d - n * 2 * n.dot(r.d)), depth, Xi));
  auto reflRay = Ray(x, r.d - n * 2 * n.dot(r.d)); // Ideal dielectric REFRACTION
  auto into = n.dot(nl) > 0;                // Ray from outside going in?
  double nc = 1;
  auto nt = 1.5, nnt = into ? nc / nt : nt / nc, ddn = r.d.dot(nl);
  double cos2t;
  if ((cos2t = 1 - nnt * nnt * (1 - ddn * ddn)) <
      0) // Total internal reflection
    return obj.e + f.mult(radiance(reflRay, depth, Xi));
  auto tdir =
      (r.d * nnt - n * ((into ? 1 : -1) * (ddn * nnt + sqrt(cos2t)))).norm();
  auto a = nt - nc, b = nt + nc, R0 = a * a / (b * b),
         c = 1 - (into ? -ddn : tdir.dot(n));
  auto Re = R0 + (1 - R0) * c * c * c * c * c, Tr = 1 - Re, P = .25 + .5 * Re,
         RP = Re / P, TP = Tr / (1 - P);
  return obj.e +
         f.mult(depth > 2
                    ? (erand48(Xi) < P ? // Russian roulette
                           radiance(reflRay, depth, Xi) * RP
                                       : radiance(Ray(x, tdir), depth, Xi) * TP)
                    : radiance(reflRay, depth, Xi) * Re +
                          radiance(Ray(x, tdir), depth, Xi) * Tr);
}
int main(int argc, char *argv[]) {
  auto w = 1024, h = 768, samps = argc == 2 ? atoi(argv[1]) / 4 : 4; // # samples
  auto cam = Ray(Vec(50, 52, 295.6), Vec(0, -0.042612, -1).norm()); // cam pos, dir
  auto cx = Vec(w * .5135 / h), cy = (cx % cam.d).norm() * .5135, *c = new Vec[w * h];
  Vec r;
#pragma omp parallel for schedule(dynamic, 1) private(r) // OpenMP
  for (auto y = 0; y < h; y++) {                          // Loop over image rows
    fprintf(stderr, "\rRendering (%d spp) %5.2f%%", samps *1,
            100. * y / (h - 1));
    for (unsigned short x = 0, Xi[3] = {0, 0, y * y * y}; x < w;
         x++) // Loop cols
      for (auto sy = 0, i = (h - y - 1) * w + x; sy < 2;
           sy++)                                    // 2x2 subpixel rows
        for (auto sx = 0; sx < 2; sx++, r = Vec()) { // 2x2 subpixel cols
          for (auto s = 0; s < samps; s++) {
            auto r1 = 2 * erand48(Xi),
                   dx = r1 < 1 ? sqrt(r1) - 1 : 1 - sqrt(2 - r1);
            auto r2 = 2 * erand48(Xi),
                   dy = r2 < 1 ? sqrt(r2) - 1 : 1 - sqrt(2 - r2);
            auto d = cx * (((sx + .5 + dx) / 2 + x) / w - .5) +
                    cy * (((sy + .5 + dy) / 2 + y) / h - .5) + cam.d;
            r = r +
                radiance(Ray(cam.o + d * 140, d.norm()), 0, Xi) * (1. / samps);
          } // Camera rays are pushed ^^^^^ forward to start in interior
          c[i] = c[i] + Vec(clamp(r.x), clamp(r.y), clamp(r.z)) * .25;
        }
  }
  auto f = fopen("image.ppm", "w"); // Write image to PPM file.
  fprintf(f, "P3\n%d %d\n%d\n", w, h, 255);
  for (auto i = 0; i < w * h; i++)
    fprintf(f, "%d %d %d ", toInt(c[i].x), toInt(c[i].y), toInt(c[i].z));
}