resource "google_artifact_registry_repository" "leios-docker" {
  location      = "us-east1"
  repository_id = "leios-docker"
  description   = "Leios docker repository"
  format        = "DOCKER"

  docker_config {
    immutable_tags = true
  }
}

resource "google_artifact_registry_repository_iam_member" "member" {
  project = google_artifact_registry_repository.leios-docker.project
  location = google_artifact_registry_repository.leios-docker.location
  repository = google_artifact_registry_repository.leios-docker.name
  role = "roles/artifactregistry.admin"
  member = "serviceAccount:${var.google_service_account}"
}

resource "google_cloud_run_v2_service" "leios_server" {
  name     = "leios-server"
  location = "us-east1"
  client   = "terraform"

  depends_on = [
    google_artifact_registry_repository.leios-docker
  ]

  template {
    containers {
      image = "us-east1-docker.pkg.dev/iog-hydra/leios-docker/input-output-hk/ouroboros-leios:4d411737776ef5f4b971fa634a32ed0930d6f7c9"
      ports {
        container_port = 8091
      }
    }

    labels = {
      "commit-sha" = "4d411737776ef5f4b971fa634a32ed0930d6f7c9"
      "managed-by" = "github-actions"
    }
  }
}

resource "google_cloud_run_service_iam_member" "noauth" {
  location = google_cloud_run_v2_service.leios_server.location
  service  = google_cloud_run_v2_service.leios_server.name
  role     = "roles/run.invoker"
  member   = "allUsers"
}

data "google_project" "project" {}

resource "google_cloud_run_domain_mapping" "leios_server_domain_mapping" {
  name     = "leios-simulation.cardano-scaling.org"
  location = google_cloud_run_v2_service.leios_server.location
  metadata {
    namespace = data.google_project.project.project_id
  }
  spec {
    route_name = google_cloud_run_v2_service.leios_server.name
  }
}
